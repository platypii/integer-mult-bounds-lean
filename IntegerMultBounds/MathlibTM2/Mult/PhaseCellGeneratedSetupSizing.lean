module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutionSizing
import Mathlib.Tactic.Ring

/-! Generated integer and coefficient widths have explicit precision bounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem generatedIntegerSetupWidth_le (p l target rhsExp : ℕ) :
    integerSetupWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionStagePrecision p l target rhsExp+2) 0 ≤
      700000*(p+l+target+rhsExp+1)^2 := by
  unfold integerSetupWidth executionPrecision executionStagePrecision executionExponent
    inputExponent sourceExponent
  ring_nf
  omega

theorem generatedCoefficientWidth_le (p l target rhsExp t u band : ℕ) :
    let W := integerSetupWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionStagePrecision p l target rhsExp+2) 0
    coefficientWorkspaceWidth (2^15*p) W t u band (4*p+1) ≤
      2000000*(p+l+target+rhsExp+1)^2+t.size+u.size+band.size := by
  have hW := generatedIntegerSetupWidth_le p l target rhsExp
  have hL := Nat.size_le.mpr (Nat.lt_two_pow_self (n := 4*p+1))
  have hrest : 700000*(p+l+target+rhsExp+1)^2+13*(2^15*p)+2*(4*p+1)+16 ≤
      2000000*(p+l+target+rhsExp+1)^2 := by
    ring_nf
    omega
  dsimp only
  unfold coefficientWorkspaceWidth
  omega

theorem generatedWeightWidth_le (p l target rhsExp t u : ℕ) :
    weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u ≤
      500000*(p+l+target+rhsExp+1)+3*t.size+u.size := by
  unfold weightWorkspaceWidth coefficientWorkspaceWidth executionPrecision executionExponent
    inputExponent sourceExponent
  simp only [Nat.size_zero]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
