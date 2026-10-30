module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundDimensions

/-! The dispatcher's existing arithmetic words have room for normalized output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN

namespace ScalarPlacement
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem FamilyDispatchInput.round_dimensions {s A : ℕ} [NeZero s]
    (p l t j : ℕ) (r : FamilyDispatchInput s A) (hj : j ≤ p+2) :
    p ≤ r.precision p l t ∧ r.precision p l t+(p+8)+5 ≤ r.width p l t ∧
      r.precision p l t-p+j+(p+(p+8)+5) ≤ r.width p l t := by
  dsimp only [FamilyDispatchInput.precision,FamilyDispatchInput.width,executionPrecision,executionWidth]
  rw [←inverseExecutionExponent_eq]
  exact inverse_round_dimensions p l r.target _ _ j hj

end ScalarPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
