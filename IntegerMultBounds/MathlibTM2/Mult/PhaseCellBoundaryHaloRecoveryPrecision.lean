module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryHaloPrecision
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryBudget

/-! Spend the retained source allowance on the second interior pass. The RHS
magnitude increase cancels, leaving a target independent of its exponent. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN

/-- The second pass's accuracy after reserving its larger RHS magnitude. -/
def boundaryHaloRecoveryTarget (p target rowCount : ℕ) : ℕ :=
  target+3*Nat.size (8*p)+Nat.size rowCount+10

theorem boundaryHaloRecoveryTarget_allowance (p u target rhsExp rowCount : ℕ) :
    boundaryHaloRecoveryTarget p target rowCount+
      recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u) =
    initialSchurTarget p u (boundaryTableBits p target rhsExp rowCount) 2+2 := by
  unfold initialSchurTarget
  rw [recoveryFirstTarget_canonical]
  unfold boundaryHaloRecoveryTarget recoveryRhsExponent couplingRowExponent stableInteriorExponent
    recoveryTarget recoveryGuardBits boundaryTableBits boundaryErrorBits
  omega

theorem boundaryHaloRecoveryTarget_accuracy (p target rowCount : ℕ) :
    recoveryTarget p target ≤ boundaryHaloRecoveryTarget p target rowCount := by
  unfold boundaryHaloRecoveryTarget recoveryTarget recoveryGuardBits
  omega

/-- The complete format, including stage headers, is reused exactly. -/
theorem boundaryHaloRecoveryTarget_sizing (p u l target rhsExp rowCount : ℕ) :
    let T := initialSchurTarget p u (boundaryTableBits p target rhsExp rowCount) 2
    let k := boundaryHaloRecoveryTarget p target rowCount
    let e := recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)
    executionPrecision p l T 2 = executionPrecision p l k e ∧
      executionStagePrecision p l T 2 = executionStagePrecision p l k e ∧
      executionWidth p l T 2 = executionWidth p l k e := by
  exact executionSizing_of_allowance p l _ _ _ _
    (boundaryHaloRecoveryTarget_allowance p u target rhsExp rowCount).symm

/-- Existing normalization guards also pay recovery coupling and rounding. -/
theorem boundaryHaloRecovery_format (p u l target rhsExp rowCount : ℕ) :
    let T := initialSchurTarget p u (boundaryTableBits p target rhsExp rowCount) 2
    let q := executionPrecision p l T 2
    let w := executionWidth p l T 2
    let e := recoveryRhsExponent p rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)
    q+e+2 ≤ w ∧
      recoveryTarget p target+couplingCountExponent p u+stableInteriorExponent p rhsExp+2 ≤ q := by
  dsimp only
  obtain ⟨_,_,hmag,hbits⟩ := boundary_normalization_precision p u l target rhsExp rowCount
  have hwidth : executionWidth p l (initialSchurTarget p u (boundaryTableBits p target rhsExp rowCount) 2) 2 =
      2*executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp rowCount) 2) 2+8 := by
    unfold executionWidth executionPrecision
    omega
  rw [hwidth]
  unfold recoveryRhsExponent couplingRowExponent stableInteriorExponent at *
  unfold recoveryTarget recoveryGuardBits boundaryTableBits boundaryErrorBits at *
  omega

/-- Boundary accuracy and the shared second-pass target pay the whole recovery
budget, including arithmetic rounding and interior stability amplification. -/
theorem boundaryHaloRecovery_error_budget (p u l target rhsExp rowCount : ℕ) :
    let solveTarget := boundaryRecoveryTarget p target
    let T := initialSchurTarget p u (boundaryTableBits p solveTarget rhsExp rowCount) 2
    let q := executionPrecision p l T 2
    let k := boundaryHaloRecoveryTarget p solveTarget rowCount
    let band := PhaseCellBand.width p u
    let ε := 3/(2 : ℝ)^solveTarget
    max (1/(2 : ℝ)^k+8*p*((2*band+1)*(2/(2 : ℝ)^q)+
      (2*band+1)*((2 : ℝ)^stableInteriorExponent p rhsExp*(1/(2 : ℝ)^q))+2*ε)) ε ≤
      1/(2 : ℝ)^target := by
  dsimp only
  have hk := boundaryHaloRecoveryTarget_accuracy p (boundaryRecoveryTarget p target) rowCount
  have hbits := (boundaryHaloRecovery_format p u l (boundaryRecoveryTarget p target) rhsExp rowCount).2
  have ht : recoveryTarget p target ≤ recoveryTarget p (boundaryRecoveryTarget p target) := by
    simp only [recoveryTarget,boundaryRecoveryTarget,recoveryGuardBits]
    omega
  have hh := recovery_error_budget_of_le (ht.trans hk) (couplingCountExponent_spec p u)
    (le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right ht _) _) _) hbits)
    (boundaryRecovery_error_budget p target)
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
