module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryBudget

/-! Accuracy of the executed recovery fields against the original cyclic principal solution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem cyclicRecovery_solution_error {s t p u l q w a n : ℕ} [NeZero s] {alpha gap : ℝ}
    (axis : RecoveryAxisBounds s t p u l alpha gap) (ha : a < s) (hn : n ≤ s)
    (hw : q+recoveryRhsExponent p 2 (stableInteriorExponent p 2)
      (couplingCountExponent p u)+2 ≤ w)
    (C : ZMod s → GaussianInt) (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^2)
    (solution : List GaussianInt) (D E : ZMod s → GaussianInt) (x xI : ZMod s → ℝ)
    (epsilon eta : ℝ) (hepsilon : 0 ≤ epsilon) :
    let band := PhaseCellBand.width p u
    let I := cyclicPrincipalInterior s t band a n
    let B := cyclicPrincipalBoundary s t band a n
    let Y := boundarySolutionField B solution
    let left := haloInterior s t band a (a+min n (s-a))
    let R := fun i => if i ∈ left then
      couplingRowField (2^15*p) q t u band a (a+min n (s-a)) true Y C i else
      couplingRowField (2^15*p) q t u band 0 (n-min n (s-a)) true Y C i
    let output := fun i => if i ∈ left then D i else E i
    (∀ i < B.card, ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) →
    (∀ i < B.card, ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ epsilon) →
    SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
      (fun i => (value q (C i)).re) →
    SchurDominance.Solves (realMatrix s t p u) I xI (fun i => (value q (R i)).re) →
    PhaseCellInterface.ErrorOn I (fun i => (value q (output i)).re) xI eta →
    PhaseCellInterface.ErrorOn I (fun i => (value q (output i)).re) x
      (eta+8*p*haloRecoveryRhsError p u q 2 epsilon) ∧
    PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (SchurDominance.glue I (fun i => (value q (output i)).re) (fun i => (value q (Y i)).re)) x
      (max (eta+8*p*haloRecoveryRhsError p u q 2 epsilon) epsilon) := by
  dsimp only
  intro hmag herror hx hxI hD
  let band := PhaseCellBand.width p u
  let I := cyclicPrincipalInterior s t band a n
  let B := cyclicPrincipalBoundary s t band a n
  let Y := boundarySolutionField B solution
  let left := haloInterior s t band a (a+min n (s-a))
  let R := fun i => if i ∈ left then
    couplingRowField (2^15*p) q t u band a (a+min n (s-a)) true Y C i else
    couplingRowField (2^15*p) q t u band 0 (n-min n (s-a)) true Y C i
  let output := fun i => if i ∈ left then D i else E i
  have hR := cyclicRecoveryRhs_spec axis ha hn hw C hC solution x epsilon hepsilon hmag herror
  have hrow (b c : ℕ) (hc : c ≤ s) (i : ZMod s) :=
    guardedCouplingRowField_eq axis.hst (2^15*p) q u band b c true hc Y C i (Or.inl rfl)
  have hRerror : ∀ i ∈ I,
      |(value q (R i)).re-((value q (C i)).re-SchurDominance.couple (realMatrix s t p u) B x i)| ≤
        haloRecoveryRhsError p u q 2 epsilon := by
    intro i hi
    have hh := (hR i hi).2.2
    change |(value q (if i ∈ left then _ else _)).re-_| ≤ _ at hh
    dsimp only [R]
    by_cases hiL : i ∈ left
    · rw [ite_eq_left hiL,hrow a _ (by omega) i] at hh
      simpa only [ite_eq_left hiL] using hh
    · rw [ite_eq_right hiL,hrow 0 _ (by omega) i] at hh
      simpa only [ite_eq_right hiL] using hh
  have hcore := cyclicRecovery_interior_error axis C R output x xI
    (haloRecoveryRhsError p u q 2 epsilon) eta hx hxI hRerror hD
  refine ⟨hcore,?_⟩
  have hpartition : I ∪ B = cyclicPrincipalVertices s a n :=
    Finset.union_sdiff_of_subset (cyclicPrincipalInterior_subset t band a n)
  rw [← hpartition]
  exact hcore.union_ite (by
    intro i hi
    simpa only [Real.norm_eq_abs] using boundarySolutionField_error q B solution x epsilon herror i hi)

/-- The existing boundary/recovery precision budget also pays the complete cyclic recovery. -/
theorem cyclicRecovery_solution_target {s t p u l a n : ℕ} [NeZero s] {alpha gap : ℝ}
    (axis : RecoveryAxisBounds s t p u l alpha gap) (ha : a < s) (hn : n ≤ s) (target : ℕ) :
    let band := PhaseCellBand.width p u
    let I := cyclicPrincipalInterior s t band a n
    let B := cyclicPrincipalBoundary s t band a n
    let solveTarget := boundaryRecoveryTarget p target
    let bits := boundaryTableBits p solveTarget 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    ∀ (C : ZMod s → GaussianInt), (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^2) →
    ∀ (solution : List GaussianInt) (D E : ZMod s → GaussianInt) (x xI : ZMod s → ℝ),
    let Y := boundarySolutionField B solution
    let left := haloInterior s t band a (a+min n (s-a))
    let R := fun i => if i ∈ left then
      couplingRowField (2^15*p) q t u band a (a+min n (s-a)) true Y C i else
      couplingRowField (2^15*p) q t u band 0 (n-min n (s-a)) true Y C i
    let output := fun i => if i ∈ left then D i else E i
    (∀ i < B.card, ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) →
    (∀ i < B.card, ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^solveTarget) →
    SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
      (fun i => (value q (C i)).re) →
    SchurDominance.Solves (realMatrix s t p u) I xI (fun i => (value q (R i)).re) →
    PhaseCellInterface.ErrorOn I (fun i => (value q (output i)).re) xI
      (1/(2 : ℝ)^recoveryTarget p bits) →
    PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (SchurDominance.glue I (fun i => (value q (output i)).re) (fun i => (value q (Y i)).re)) x
      (1/(2 : ℝ)^target) := by
  dsimp only
  intro C hC solution D E x xI hmag herror hx hxI hD
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let solveTarget := boundaryRecoveryTarget p target
  let bits := boundaryTableBits p solveTarget 2 B.card
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hw := recovery_coupling_width p l (recoveryTarget p bits) 2
    (stableInteriorExponent p 2) (couplingCountExponent p u)
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  have hw' : q+recoveryRhsExponent p 2 (stableInteriorExponent p 2)
      (couplingCountExponent p u)+2 ≤ w := by
    have hwidth : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
    rw [hwidth]
    exact hw
  have h := cyclicRecovery_solution_error (w := w) axis ha hn hw' C hC solution D E x xI
    (3/(2 : ℝ)^solveTarget) (1/(2 : ℝ)^recoveryTarget p bits) (by positivity)
    hmag herror hx hxI hD
  have hbudget := boundaryRecovery_published_error_budget p u l target B.card
  intro i hi
  exact (h.2 i hi).trans hbudget

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
