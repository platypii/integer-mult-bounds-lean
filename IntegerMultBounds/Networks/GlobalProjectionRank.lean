import IntegerMultBounds.Networks.ProjectionTrace
import IntegerMultBounds.Networks.GlobalRankStages
import IntegerMultBounds.Networks.GlobalLabelsNondegenerate
import IntegerMultBounds.Networks.NetworkBudget

/-! Actual projection-difference ranks for the physically labeled three-stage
network. Scalar gates, incidences, labels, and terminal dimensions are the
existing constructions; no global rank or loss estimate is a hypothesis. -/

namespace IntegerMultBounds.Networks.GlobalProjectionRank

open scoped TensorProduct
open Module GroupedFrames GlobalLabels

section Labels
variable {K F B A C : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F]
  (D : LinearMap.BilinForm K F) (hs : D.IsSymm) (hn : D.Nondegenerate)
  (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)

def cubeForm : LinearMap.BilinForm K (StageLabels.Ambient K F) :=
  TensorSubspace.form D (TensorSubspace.form D D)

omit [FiniteDimensional K F] in
include hs in
theorem cube_symm : (cubeForm D).IsSymm :=
  LinearMap.BilinForm.isSymm_iff.mpr ((LinearMap.BilinForm.isSymm_iff.mp hs).tmul
    ((LinearMap.BilinForm.isSymm_iff.mp hs).tmul (LinearMap.BilinForm.isSymm_iff.mp hs)))

include hn in
theorem cube_nondegenerate : (cubeForm D).Nondegenerate :=
  Labels.tmul_nondegenerate D (TensorSubspace.form D D) hn (Labels.tmul_nondegenerate D D hn hn)

omit [FiniteDimensional K F] in
include ht in
theorem terminal_nondegenerate (b : GlobalCircuit.Address B) :
    ((cubeForm D).restrict (terminal (K := K) t b)).Nondegenerate := by
  apply Labels.line_nondegenerate
  simpa only [cubeForm, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul] using
    mul_ne_zero (mul_ne_zero (ht b.2.2) (ht b.2.1)) (ht b.1)

omit [FiniteDimensional K F] in
include ht in
theorem source_nondegenerate (i : GlobalCircuit.World B A C) :
    ((cubeForm D).restrict (source t i)).Nondegenerate := by
  rcases i with b | b | s
  · exact terminal_nondegenerate D t ht b
  · exact MotifLabels.bot_nondegenerate _
  · exact MotifLabels.bot_nondegenerate _

include hs hn ht in
theorem sink_nondegenerate (i : GlobalCircuit.World B A C) :
    ((cubeForm D).restrict (sink D t i)).Nondegenerate := by
  rcases i with b | b | s
  · exact MotifLabels.top_nondegenerate _ (cube_nondegenerate D hn)
  · exact ProjectionRank.orthogonal_nondegenerate _ (cube_symm D hs)
      (cube_nondegenerate D hn) _ (terminal_nondegenerate D t ht b)
  · exact MotifLabels.top_nondegenerate _ (cube_nondegenerate D hn)
end Labels

section Schedule
variable {K F B A C R : Type*} [Field K] [AddCommGroup F] [Module K F]
  [FiniteDimensional K F] [Fintype B] [Fintype A] [Fintype C]
  [DecidableEq B] [DecidableEq A] [DecidableEq C] [CommRing R] [Nontrivial R] [DecidableEq R]
  {n a c : ℕ}
  (D : LinearMap.BilinForm K F) (hs : D.IsSymm) (hn : D.Nondegenerate)
  (t : B → F) (ht : ∀ b, D (t b) (t b) ≠ 0)
  (eB : Fin n ≃ B) (eA : Fin a ≃ A) (eC : Fin c ≃ C)
  (owner : Fin a → Fin n) (G : Fin c → Fin n → R)
  (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

/-- The literal update list of all physically grouped gates and final sinks. -/
def trace (wires : List (GlobalCircuit.World B A C)) :=
  networkUpdates wires (sink D t) (program D hs hn t ht eB eA eC owner G J H)

omit [Fintype B] [Fintype A] [Fintype C] [DecidableEq B] [DecidableEq A]
  [DecidableEq C] [Nontrivial R] in
theorem trace_nondegenerate (wires : List (GlobalCircuit.World B A C)) :
    ∀ p ∈ trace D hs hn t ht eB eA eC owner G J H wires,
      ((cubeForm D).restrict p.2).Nondegenerate := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨v, hv, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact program_nondegenerate D hs hn t ht eB eA eC owner G J H v hv
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact sink_nondegenerate D hs hn t ht i

/-- Sum the ranks of actual projection differences on the actual edge list. -/
noncomputable def rankSum (wires : List (GlobalCircuit.World B A C)) : ℕ :=
  ((RankTrace.edges (source t) (trace D hs hn t ht eB eA eC owner G J H wires)).map
    (fun p => ProjectionTrace.edgeRank (cubeForm D) (cube_symm D hs) p.1 p.2)).sum

omit [Fintype B] [Fintype A] [Fintype C] [Nontrivial R] in
/-- Sink alignment ends at the actual prescribed physical output profile. -/
theorem trace_final (wires : List (GlobalCircuit.World B A C)) (hall : ∀ i, i ∈ wires) :
    RankTrace.finish (source t) (trace D hs hn t ht eB eA eC owner G J H wires) = sink D t :=
  network_trace_final wires hall (source t) (sink D t) _

variable (target : Fin a → Fin n)
  (hJ : ∀ i p, J i p ≠ 0 ↔ target p = i)
  (hneigh : ∀ p, D (t (eB (owner p))) (t (eB (target p))) = 0)

include hJ hneigh

/-- Genuine projection ranks balance the physical source and sink dimensions,
with twice the actual loss of the compiled trace. -/
theorem rank_balance (wires : List (GlobalCircuit.World B A C)) (hall : ∀ i, i ∈ wires) :
    rankSum D hs hn t ht eB eA eC owner G J H wires +
        RankTrace.total (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U) (source (A := A) (C := C) t) =
      RankTrace.total (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U) (sink (A := A) (C := C) D t) +
        2 * RankTrace.loss (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U)
          (source t) (trace D hs hn t ht eB eA eC owner G J H wires) := by
  have hb := ProjectionTrace.rank_balance (cubeForm D) (cube_symm D hs) (source t)
    (trace D hs hn t ht eB eA eC owner G J H wires)
    (source_nondegenerate D t ht) (trace_nondegenerate D hs hn t ht eB eA eC owner G J H wires)
    (GlobalRank.network_comparable D hs hn t ht eB eA eC owner G J H target hJ hneigh wires)
  rw [trace_final D hs hn t ht eB eA eC owner G J H wires hall] at hb
  exact hb

/-- The actual trace balance with all terminal dimensions evaluated. -/
theorem rank_balance_dimensions (wires : List (GlobalCircuit.World B A C))
    (hall : ∀ i, i ∈ wires) :
    rankSum D hs hn t ht eB eA eC owner G J H wires + Fintype.card B ^ 3 + Fintype.card B ^ 3 =
      Fintype.card (GlobalCircuit.World B A C) * (finrank K F) ^ 3 +
        2 * RankTrace.loss (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U)
          (source t) (trace D hs hn t ht eB eA eC owner G J H wires) := by
  have hb := rank_balance D hs hn t ht eB eA eC owner G J H target hJ hneigh wires hall
  rw [NetworkBudget.source_total D t ht] at hb
  have he := NetworkBudget.sink_total (A := A) (C := C) D hn t ht
  omega

/-- Global rank bound from the proved three-stage loss estimate, with no
assumed local or global rank budget. -/
theorem rank_le_dimensions (wires : List (GlobalCircuit.World B A C)) (hall : ∀ i, i ∈ wires) :
    rankSum D hs hn t ht eB eA eC owner G J H wires + 2 * Fintype.card B ^ 3 ≤
      Fintype.card (GlobalCircuit.World B A C) * (finrank K F) ^ 3 +
        6 * n ^ 2 * c * finrank K F := by
  have hb := rank_balance_dimensions D hs hn t ht eB eA eC owner G J H target hJ hneigh wires hall
  have hl := GlobalRank.network_loss_le D hs hn t ht eB eA eC owner G J H target hJ hneigh wires
  change RankTrace.loss (fun U : Submodule K (StageLabels.Ambient K F) => finrank K U)
    (source t) (trace D hs hn t ht eB eA eC owner G J H wires) ≤ _ at hl
  have hm : 6 * n ^ 2 * c * finrank K F = 2 * (3 * n ^ 2 * c * finrank K F) := by ring
  rw [hm]
  omega

end Schedule
end IntegerMultBounds.Networks.GlobalProjectionRank
