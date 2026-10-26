module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowFits
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStableInteriorBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupportBudget

/-! Derive the residual storage width from the shared arithmetic exponent. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem interiorResidual_width {p l target rhsExp countExp : ℕ}
    (hcount : countExp ≤ executionExponent p l target rhsExp) :
    executionPrecision p l target rhsExp+
      couplingRowExponent rhsExp (interiorOutputExponent p l target rhsExp) (8*p+1) countExp+2 ≤
        executionWidth p l target rhsExp := by
  dsimp [executionPrecision,executionWidth,couplingRowExponent,interiorOutputExponent,
    executionExponent,inputExponent,sourceExponent] at *
  omega

theorem stableInteriorExponent_le_outputExponent (p l target rhsExp : ℕ) :
    stableInteriorExponent p rhsExp ≤ interiorOutputExponent p l target rhsExp := by
  dsimp [stableInteriorExponent,interiorOutputExponent,executionExponent,inputExponent,sourceExponent]
  omega

theorem stableInteriorResidual_width (p u l target rhsExp : ℕ) :
    executionPrecision p l target rhsExp+
      couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)+2 ≤
        executionWidth p l target rhsExp := by
  have hwide := interiorResidual_width (p := p) (l := l) (target := target) (rhsExp := rhsExp)
    (couplingCountExponent_le_execution p u l target rhsExp)
  have he := stableInteriorExponent_le_outputExponent p l target rhsExp
  dsimp only [couplingRowExponent] at hwide ⊢
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
