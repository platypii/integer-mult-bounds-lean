module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPublicationField

/-! Join the two second-pass certificates before applying the shared cyclic
recovery budget. This is independent of the physical assembly schedule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem cyclicRecovery_pieces_target {s t p u l a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s) (target : ℕ) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let solveTarget := boundaryRecoveryTarget p target
    let q := executionPrecision p l (initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2) 2
    let k := boundaryHaloRecoveryTarget p solveTarget B.card
    let left := haloInterior s t band a (a+min n (s-a))
    let right := haloInterior s t band 0 (n-min n (s-a))
    ∀ (C : ZMod s → GaussianInt), (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^2) →
    ∀ (solution : List GaussianInt) (D E : ZMod s → GaussianInt) (x xL xR : ZMod s → ℝ),
    let Y := boundarySolutionField B solution
    (∀ i < B.card, ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) →
    (∀ i < B.card, ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^solveTarget) →
    SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x (fun i => (value q (C i)).re) →
    SchurDominance.Solves (realMatrix s t p u) left xL (fun i => (value q
      (guardedCouplingRowField (2^15*p) q t u band a (a+min n (s-a)) true Y C i)).re) →
    SchurDominance.Solves (realMatrix s t p u) right xR (fun i => (value q
      (guardedCouplingRowField (2^15*p) q t u band 0 (n-min n (s-a)) true Y C i)).re) →
    PhaseCellInterface.ErrorOn left (fun i => (value q (D i)).re) xL (1/(2 : ℝ)^k) →
    PhaseCellInterface.ErrorOn right (fun i => (value q (E i)).re) xR (1/(2 : ℝ)^k) →
    PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (fun i => (value q (cyclicPublicationField t band a n D E Y i)).re) x (1/(2 : ℝ)^target) := by
  dsimp only
  intro C hC solution D E x xL xR hmag herror hx hxL hxR hD hE
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let q := executionPrecision p l (initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p target) 2 B.card) 2) 2
  let left := haloInterior s t band a (a+min n (s-a))
  let right := haloInterior s t band 0 (n-min n (s-a))
  let Y := boundarySolutionField B solution
  let R := fun i => if i ∈ left then
    couplingRowField (2^15*p) q t u band a (a+min n (s-a)) true Y C i else
    couplingRowField (2^15*p) q t u band 0 (n-min n (s-a)) true Y C i
  let xI := fun i => if i ∈ left then xL i else xR i
  let output := fun i => if i ∈ left then D i else E i
  have hdisjoint : Disjoint left right := (cyclicPrincipalPieces_disjoint a n ha hn).mono
    (haloInterior_subset s t band a _) (haloInterior_subset s t band 0 _)
  have hnot (i : ZMod s) (hi : i ∈ right) : i ∉ left := fun hj => Finset.disjoint_left.mp hdisjoint hj hi
  have hrow (b c : ℕ) (hc : c ≤ s) (i : ZMod s) :=
    guardedCouplingRowField_eq axis.hst (2^15*p) q u band b c true hc Y C i (Or.inl rfl)
  have hsolve : SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalInterior s t band a n) xI
      (fun i => (value q (R i)).re) := by
    apply cyclicPrincipalInterior_solves p u a n ha hn xL xR _
    · intro i hi
      have hiL : i ∈ left := hi
      have hh := hxL i hi
      change _ = (value q (guardedCouplingRowField (2^15*p) q t u band a (a+min n (s-a)) true Y C i)).re at hh
      rw [hrow a _ (by omega) i] at hh
      simpa only [R,ite_eq_left hiL] using hh
    · intro i hi
      have hh := hxR i hi
      change _ = (value q (guardedCouplingRowField (2^15*p) q t u band 0 (n-min n (s-a)) true Y C i)).re at hh
      rw [hrow 0 _ (by omega) i] at hh
      simpa only [R,ite_eq_right (hnot i hi)] using hh
  have hjoined : PhaseCellInterface.ErrorOn (cyclicPrincipalInterior s t band a n)
      (fun i => (value q (output i)).re) xI
      (1/(2 : ℝ)^boundaryHaloRecoveryTarget p (boundaryRecoveryTarget p target) B.card) := by
    intro i hi
    by_cases hiL : i ∈ left
    · simpa only [output,xI,ite_eq_left hiL] using hD i hiL
    · have hiR : i ∈ right := (Finset.mem_union.mp hi).resolve_left hiL
      simpa only [output,xI,ite_eq_right hiL] using hE i hiR
  have h := cyclicRecovery_solution_shared_target axis ha hn target C hC solution D E x xI hmag herror hx hsolve hjoined
  apply cyclicPublicationField_accuracy q t band a n D E Y x _
  simpa only [apply_ite] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
