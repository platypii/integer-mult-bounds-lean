module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowFits
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStableInteriorBounds

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

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
