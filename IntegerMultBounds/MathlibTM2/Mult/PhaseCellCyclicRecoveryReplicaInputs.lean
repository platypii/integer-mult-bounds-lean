module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoupledReplicaProblem
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryRows

/-! The actual joint-boundary recovery archive is the reverse source of an
ordinary second-pass replica problem. Both pieces use the joint boundary count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem cyclicRecoveryReplicaInputs {s t p u l A : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (target origin span : ℕ) (hfit : origin+span ≤ s)
    (B : Finset (ZMod s)) (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ i,
      ‖value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 B.card) 2) 2)
        (F i)‖ ≤ (2 : ℝ)^2)
    (solutions : List (List GaussianInt)) (hlen : solutions.length = Fs.length)
    (hmag : ∀ solution ∈ solutions, ∀ i < B.card,
      ‖value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 B.card) 2) 2)
        (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) :
    let T := initialSchurTarget p u (boundaryTableBits p target 2 B.card) 2
    let H := axis.replicaProblem T 2 origin span hfit Fs hF
    let rows := cyclicBoundaryRecoveryRows B solutions Fs
    ∃ J : ReplicaHaloProblem s, H.SameLayout J ∧
      J.target = boundaryHaloRecoveryTarget p target B.card ∧
      J.rhsExp = recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u) ∧
      J.Fs = rows.map (fun row => guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
        H.origin (H.origin+H.span) true row.1 row.2.1) ∧
      J.Fs.reverse.flatMap (cyclicRecoveryField (A := A) H) = rows.reverse.flatMap (cyclicRecoveryOutputL H) ∧
      J.Fs.reverse.flatMap (cyclicRecoveryField (A := A) H) = rows.reverse.flatMap (cyclicRecoveryOutputR H) := by
  dsimp only
  let T := initialSchurTarget p u (boundaryTableBits p target 2 B.card) 2
  let H := axis.replicaProblem T 2 origin span hfit Fs hF
  let rows := cyclicBoundaryRecoveryRows B solutions Fs
  let pairs := rows.map (fun row => (row.1,row.2.1))
  have hboundF : ∀ row ∈ pairs, ∀ i, ‖value H.precision (row.2 i)‖ ≤ (2 : ℝ)^2 := by
    intro row hr i
    change row ∈ rows.map (fun row : CyclicRecoveryRow s => (row.1,row.2.1)) at hr
    obtain ⟨r,hr,he⟩ : ∃ r ∈ rows, (r.1,r.2.1) = row := List.mem_map.mp hr
    rw [← he]
    obtain ⟨pair,hpair,heR⟩ : ∃ pair ∈ (solutions.zip Fs).reverse,
      (boundarySolutionField B pair.1,(pair.2,pair.2)) = r := List.mem_map.mp hr
    rw [← heR]
    exact hF pair.2 (List.of_mem_zip (List.mem_reverse.mp hpair)).2 i
  have hboundY : ∀ row ∈ pairs, ∀ i,
      ‖value H.precision (row.1 i)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2 := by
    intro row hr i
    change row ∈ rows.map (fun row : CyclicRecoveryRow s => (row.1,row.2.1)) at hr
    obtain ⟨r,hr,he⟩ : ∃ r ∈ rows, (r.1,r.2.1) = row := List.mem_map.mp hr
    rw [← he]
    obtain ⟨pair,hpair,heR⟩ : ∃ pair ∈ (solutions.zip Fs).reverse,
      (boundarySolutionField B pair.1,(pair.2,pair.2)) = r := List.mem_map.mp hr
    rw [← heR]
    exact boundarySolutionField_magnitude H.precision (stableInteriorExponent p 2) B pair.1
      (hmag pair.1 (List.of_mem_zip (List.mem_reverse.mp hpair)).1) i
  let J := axis.cyclicPieceRecoveryProblem target B.card origin span hfit pairs hboundF hboundY
  have hcount : pairs.length = Fs.length := by
    simpa only [pairs,List.length_map] using cyclicBoundaryRecoveryRows_length B solutions Fs hlen
  have hlayout : H.SameLayout J := axis.cyclicPieceRecoveryProblem_layout
    target B.card origin span hfit Fs hF pairs hboundF hboundY hcount
  have hFs : J.Fs = rows.map (fun row => guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
      H.origin (H.origin+H.span) true row.1 row.2.1) := by
    change (rows.map (fun row => (row.1,row.2.1))).map _ = _
    simp only [List.map_map]
    rfl
  have hstream : J.Fs.reverse.flatMap (cyclicRecoveryField (A := A) H) =
      rows.reverse.flatMap (cyclicRecoveryOutputL H) := by
    rw [hFs,←List.map_reverse,List.flatMap_map]
    rfl
  refine ⟨J,hlayout,rfl,rfl,hFs,hstream,?_⟩
  rw [hstream]
  apply List.flatMap_congr
  intro row hr
  have hr' : row ∈ rows := List.mem_reverse.mp hr
  change row ∈ (solutions.zip Fs).reverse.map (fun pair => (boundarySolutionField B pair.1,(pair.2,pair.2))) at hr'
  obtain ⟨pair,_,rfl⟩ := List.mem_map.mp hr'
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
