module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutionSizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStableInteriorBounds

/-! Canonical execution widths pay for both periodic coupling input formats. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem execution_couplingCoefficient_width (p l target rhsExp : ℕ) :
    executionPrecision p l target rhsExp+(8*p+1)+2 ≤ executionWidth p l target rhsExp := by
  unfold executionPrecision executionWidth executionExponent inputExponent sourceExponent
  omega

theorem execution_couplingInput_width (p l target rhsExp : ℕ) :
    executionPrecision p l target rhsExp+stableInteriorExponent p rhsExp+2 ≤
      executionWidth p l target rhsExp := by
  unfold executionPrecision executionWidth executionExponent inputExponent sourceExponent stableInteriorExponent
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
