module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizationBudget

/-! Conserve source allowance when sharing working precision between the raw
halo RHS and the normalized boundary factor setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN

def boundaryHaloTarget (p u target rhsExp rowCount : ℕ) : ℕ :=
  initialSchurTarget p u (boundaryTableBits p target rhsExp rowCount) 2+2-rhsExp

/-- Moving the RHS exponent into the target leaves the working format unchanged. -/
theorem executionSizing_of_allowance (p l j rhsExp j' rhsExp' : ℕ)
    (hallowance : j+rhsExp = j'+rhsExp') :
    executionPrecision p l j rhsExp = executionPrecision p l j' rhsExp' ∧
      executionStagePrecision p l j rhsExp = executionStagePrecision p l j' rhsExp' ∧
      executionWidth p l j rhsExp = executionWidth p l j' rhsExp' := by
  have hsource : sourceExponent l j rhsExp = sourceExponent l j' rhsExp' := by
    unfold sourceExponent
    omega
  have he : executionExponent p l j rhsExp = executionExponent p l j' rhsExp' := by
    unfold executionExponent
    rw [hsource]
  exact ⟨congrArg (fun e => 4*e) he,congrArg (fun e => 2*e) he,
    congrArg (fun e => 8*e+8) he⟩

theorem boundaryHaloTarget_allowance (p u target rhsExp rowCount : ℕ) :
    boundaryHaloTarget p u target rhsExp rowCount+rhsExp =
      initialSchurTarget p u (boundaryTableBits p target rhsExp rowCount) 2+2 := by
  unfold boundaryHaloTarget initialSchurTarget
  rw [recoveryFirstTarget_canonical]
  unfold recoveryTarget recoveryGuardBits boundaryTableBits boundaryErrorBits
  omega

/-- The shared format pays at least the manuscript's initial Schur accuracy. -/
theorem boundaryHaloTarget_accuracy (p u target rhsExp rowCount : ℕ) :
    initialSchurTarget p u target rhsExp ≤ boundaryHaloTarget p u target rhsExp rowCount := by
  unfold boundaryHaloTarget initialSchurTarget
  rw [recoveryFirstTarget_canonical,recoveryFirstTarget_canonical]
  unfold recoveryTarget recoveryGuardBits boundaryTableBits boundaryErrorBits
  omega

theorem boundaryHaloTarget_sizing (p u l target rhsExp rowCount : ℕ) :
    let j := boundaryHaloTarget p u target rhsExp rowCount
    let T := initialSchurTarget p u (boundaryTableBits p target rhsExp rowCount) 2
    executionPrecision p l j rhsExp = executionPrecision p l T 2 ∧
      executionStagePrecision p l j rhsExp = executionStagePrecision p l T 2 ∧
      executionWidth p l j rhsExp = executionWidth p l T 2 := by
  exact executionSizing_of_allowance p l _ _ _ _
    (boundaryHaloTarget_allowance p u target rhsExp rowCount)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
