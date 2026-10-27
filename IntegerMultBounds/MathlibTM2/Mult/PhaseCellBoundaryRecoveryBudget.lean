module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryErrorBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitialErrorBudget

/-! Align the computed boundary solve with the shared recovery arithmetic bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN

/-- Two extra solve bits pay the three boundary approximation errors. -/
def boundaryRecoveryTarget (p target : ℕ) : ℕ := recoveryTarget p target+2

theorem boundaryRecovery_error_budget (p target : ℕ) :
    3/(2 : ℝ)^boundaryRecoveryTarget p target ≤ 1/(2 : ℝ)^recoveryTarget p target := by
  dsimp [boundaryRecoveryTarget]
  rw [pow_add]
  have hpos : (0 : ℝ) < 2^recoveryTarget p target := by positivity
  apply (div_le_div_iff₀ (by positivity) hpos).mpr
  norm_num
  linarith

theorem boundaryRecovery_workingTarget (p target N : ℕ) :
    target ≤ boundaryTableBits p (boundaryRecoveryTarget p target) 2 N := by
  dsimp [boundaryTableBits,boundaryErrorBits,boundaryRecoveryTarget,recoveryTarget]
  omega

/-- The boundary solve and recovery use exactly the same precision and headers. -/
theorem boundaryRecovery_shared_target (p u target N : ℕ) :
    initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 N) 2 =
      recoveryFirstTarget p
        (recoveryTarget p (boundaryTableBits p (boundaryRecoveryTarget p target) 2 N))
        2 (stableInteriorExponent p 2) (couplingCountExponent p u) := rfl

/-- The actual boundary error and retained precision pay the complete halo recovery error. -/
theorem boundaryRecovery_published_error_budget (p u l target N : ℕ) :
    let solveTarget := boundaryRecoveryTarget p target
    let bits := boundaryTableBits p solveTarget 2 N
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let band := PhaseCellBand.width p u
    max (1/(2 : ℝ)^recoveryTarget p bits+8*p*((2*band+1)*(2/(2 : ℝ)^q)+
      (2*band+1)*((2 : ℝ)^stableInteriorExponent p 2*(1/(2 : ℝ)^q))+
      2*(3/(2 : ℝ)^solveTarget))) (3/(2 : ℝ)^solveTarget) ≤ 1/(2 : ℝ)^target := by
  exact selected_recovery_error_budget_of_le p u l target
    (boundaryTableBits p (boundaryRecoveryTarget p target) 2 N) 2 (stableInteriorExponent p 2)
    (boundaryRecovery_workingTarget p target N) (boundaryRecovery_error_budget p target)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
