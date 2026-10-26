module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutionSizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowFits

/-! Share one arithmetic/header bank between the initial and recovery interior passes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.NLogN

def recoveryRhsExponent (p rhsExp boundaryExp countExp : ℕ) : ℕ :=
  couplingRowExponent rhsExp boundaryExp (8*p+1) countExp

/-- Reserve the recovery magnitude increase in the first pass's accuracy target. -/
def recoveryFirstTarget (p target rhsExp boundaryExp countExp : ℕ) : ℕ :=
  target+(recoveryRhsExponent p rhsExp boundaryExp countExp-rhsExp)

theorem recovery_execution_exponent (p l target rhsExp boundaryExp countExp : ℕ) :
    executionExponent p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp =
      executionExponent p l target (recoveryRhsExponent p rhsExp boundaryExp countExp) := by
  dsimp [executionExponent,inputExponent,sourceExponent,recoveryFirstTarget,
    recoveryRhsExponent,couplingRowExponent]
  omega

theorem recovery_execution_sizes (p l target rhsExp boundaryExp countExp : ℕ) :
    executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp =
      executionPrecision p l target (recoveryRhsExponent p rhsExp boundaryExp countExp) ∧
    executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp =
      executionStagePrecision p l target (recoveryRhsExponent p rhsExp boundaryExp countExp) ∧
    executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp =
      executionWidth p l target (recoveryRhsExponent p rhsExp boundaryExp countExp) := by
  simp only [executionPrecision,executionStagePrecision,executionWidth,
    recovery_execution_exponent,and_self]

theorem recovery_coupling_width (p l target rhsExp boundaryExp countExp : ℕ) :
    let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp countExp) rhsExp
    q+recoveryRhsExponent p rhsExp boundaryExp countExp+2 ≤ 2*q+8 := by
  dsimp only
  rw [(recovery_execution_sizes p l target rhsExp boundaryExp countExp).1]
  dsimp [executionPrecision,executionExponent,inputExponent,sourceExponent]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
