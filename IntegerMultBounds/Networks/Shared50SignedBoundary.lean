import IntegerMultBounds.Networks.Shared50GlobalTrace
import IntegerMultBounds.Networks.SignedProjection
import IntegerMultBounds.Networks.ShearFrame
import IntegerMultBounds.Networks.FramedEdgeTrace

/-! The actual first boundary admits the rational negative-source correction.
Its operators are genuine projector sums, and their ranks exceed the ordinary
boundary ranks by exactly the physical source dimension total. -/

namespace IntegerMultBounds.Networks.Shared50SignedBoundary

noncomputable section
open Module Shared50GlobalTrace
open Shared50GlobalBudget (World Ambient sourceTotal)
open Shared50ReuseLabels (cubeForm cube_symm)

abbrev projector (U : Label) : Ambient →ₗ[ℚ] Ambient :=
  ProjectionTrace.projector cubeForm cube_symm U

/-- The signed physical source-to-first-stage shear matrix at each wire. -/
def operator (i : World) : Ambient →ₗ[ℚ] Ambient :=
  projector (input 0 i) - (-projector (source i))

/-- The sign correction is valid even when the first stage label strictly
contains the source label. All nondegeneracy and inclusion facts are proved. -/
theorem operator_rank (i : World) :
    finrank ℚ (LinearMap.range (operator i)) =
      ProjectionTrace.edgeRank cubeForm cube_symm (source i) (input 0 i) +
        finrank ℚ (source i) := by
  unfold operator ProjectionTrace.edgeRank projector
  rw [ProjectionTrace.projector_eq _ _ _ (source_nondegenerate i),
    ProjectionTrace.projector_eq _ _ _ (input_nondegenerate 0 i)]
  exact ProjectionRank.negative_source_edge_extra cubeForm cube_symm (by norm_num)
    _ _ (source_nondegenerate i) (input_nondegenerate 0 i) (source_le_input i)

/-- Actual sum of signed first-boundary operator ranks, over every physical wire. -/
def rankSum : ℕ := RankTrace.total (fun op : Ambient →ₗ[ℚ] Ambient => finrank ℚ (LinearMap.range op)) operator

def ordinaryRankSum : ℕ :=
  RankTrace.total (fun p : Label × Label => ProjectionTrace.edgeRank cubeForm cube_symm p.1 p.2)
    (fun i : World => (source i,input 0 i))

private theorem totals_extra {ι A B C : Type*} [Fintype ι]
    (da : A → ℕ) (db : B → ℕ) (dc : C → ℕ) (a : ι → A) (b : ι → B) (c : ι → C)
    (h : ∀ i, da (a i) = db (b i) + dc (c i)) :
    RankTrace.total da a = RankTrace.total db b + RankTrace.total dc c := by
  unfold RankTrace.total
  simp_rw [h]
  exact Finset.sum_add_distrib

theorem rankSum_eq : rankSum = ordinaryRankSum + sourceTotal := by
  have hh := totals_extra (fun op : Ambient →ₗ[ℚ] Ambient => finrank ℚ (LinearMap.range op))
    (fun p : Label × Label => ProjectionTrace.edgeRank cubeForm cube_symm p.1 p.2)
    (fun U : Label => finrank ℚ U) operator (fun i : World => (source i,input 0 i)) source operator_rank
  have ha : RankTrace.total (fun op : Ambient →ₗ[ℚ] Ambient => finrank ℚ (LinearMap.range op)) operator = rankSum := rfl
  have hb : RankTrace.total (fun p : Label × Label => ProjectionTrace.edgeRank cubeForm cube_symm p.1 p.2)
      (fun i : World => (source i,input 0 i)) = ordinaryRankSum := rfl
  have hc : RankTrace.total (fun U : Label => finrank ℚ U) source = sourceTotal := rfl
  rw [ha,hb,hc] at hh
  exact hh

/-- These counted matrices are exactly the actual signed address-frame changes. -/
theorem frame_change (i : World) (f : (Ambient × Ambient) → ZMod 2) :
    ShearFrame.frame (projector (input 0 i))
      ((ShearFrame.frame (-projector (source i))).symm f) =
        ShearFrame.frame (operator i) f :=
  ShearFrame.frame_change _ _ _

/-- A once-per-wire alignment retains its original old/new pair at every
listed wire; no earlier update can have changed a later wire. -/
private theorem edges_alignment {ι L : Type*} [DecidableEq ι]
    (current desired : ι → L) (xs : List ι) (hn : xs.Nodup) :
    RankTrace.edges current (xs.map (fun i => (i,desired i))) =
      xs.map (fun i => (current i,desired i)) := by
  induction xs generalizing current with
  | nil => rfl
  | cons i xs ih =>
    obtain ⟨hi,ht⟩ := List.nodup_cons.mp hn
    simp only [List.map_cons,RankTrace.edges]
    rw [ih _ ht]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    simp only [Function.update_of_ne hji]

/-- The concrete first boundary uses exactly this pair for each physical wire. -/
theorem first_edges :
    RankTrace.edges source (boundaryUpdates 0) = wires.map (fun i => (source i,input 0 i)) :=
  edges_alignment source (input 0) wires (Finset.nodup_toList _)

private theorem sum_enumeration {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    (Finset.univ.toList.map f).sum = ∑ i, f i := by
  classical
  simp

/-- Ordered signed matrices, one for every actual first-boundary alignment. -/
def operators : List (Ambient →ₗ[ℚ] Ambient) := wires.map operator

/-- The per-wire ordinary sum is the rank sum of the actual boundary trace. -/
theorem ordinaryRankSum_eq_trace :
    ordinaryRankSum = ProjectionTrace.rankSum cubeForm cube_symm source (boundaryUpdates 0) := by
  rw [ProjectionTrace.rankSum,first_edges,List.map_map]
  exact (sum_enumeration (fun i : World => ProjectionTrace.edgeRank cubeForm cube_symm (source i) (input 0 i))).symm

theorem operators_rankSum :
    (operators.map (fun op => finrank ℚ (LinearMap.range op))).sum = rankSum := by
  rw [operators,List.map_map]
  exact sum_enumeration (fun i : World => finrank ℚ (LinearMap.range (operator i)))

/-- The signed ordered list changes the actual first-boundary rank sum by
precisely the already-proved physical source total. -/
theorem operators_rankSum_eq_trace :
    (operators.map (fun op => finrank ℚ (LinearMap.range op))).sum =
      ProjectionTrace.rankSum cubeForm cube_symm source (boundaryUpdates 0) + sourceTotal := by
  rw [operators_rankSum,rankSum_eq,ordinaryRankSum_eq_trace]

/-- Literal physical address-frame changes on the first boundary's actual
wire enumeration, starting from the prescribed negative source projectors. -/
def physical : List (FramedCircuit.Instruction World (ZMod 2) ((Ambient × Ambient) → ZMod 2)) :=
  FramedCircuit.edges (fun i => ShearFrame.frame (-projector (source i)))
    (fun i => ShearFrame.frame (projector (input 0 i))) wires

private theorem alignment_pairs {ι V : Type*} [DecidableEq ι] [AddCommGroup V] [Module (ZMod 2) V]
    (current desired : ι → FramedCircuit.Frame (ZMod 2) V) (xs : List ι) (hn : xs.Nodup) :
    FramedEdgeTrace.pairs (FramedCircuit.edges current desired xs) =
      xs.map (fun i => (current i,desired i)) := by
  have hh := FramedEdgeTrace.pairs_edges (fun f : FramedCircuit.Frame (ZMod 2) V => f) current desired xs
  rw [edges_alignment current desired xs hn,List.map_map] at hh
  exact hh

theorem physical_pairs : FramedEdgeTrace.pairs physical =
    wires.map (fun i => (ShearFrame.frame (-projector (source i)),ShearFrame.frame (projector (input 0 i)))) :=
  alignment_pairs _ _ wires (Finset.nodup_toList _)

/-- Every actual physical signed edge has exactly its counted shear matrix,
in precisely the enumeration used by the ordinary first boundary. -/
theorem physical_realizes : List.Forall₂
    (fun p op => ∀ f, p.2 (p.1.symm f) = ShearFrame.frame op f)
    (FramedEdgeTrace.pairs physical) operators := by
  rw [physical_pairs,operators,List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
  exact fun i _ => frame_change i

end
end IntegerMultBounds.Networks.Shared50SignedBoundary
