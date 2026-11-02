module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicTransposePlan

/-! Separate a rectangle's full-width stages from its Euclidean remainder. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- Exactly `q` full-width peel steps, followed by an exact residual transpose.
The trailing block grows structurally; the payload volume is unchanged. -/
def dyadicTransposeSplitPlan (q r b W : ℕ) (hb : 0 < b) :
    DyadicTransposePlan (q*b+r) b W :=
  match q with
  | 0 => (show r = 0*b+r by omega) ▸ dyadicTransposePlan (r+b) r b W (by omega)
  | q+1 =>
      (show (q*b+r)+b = (q+1)*b+r by ring) ▸
        .left hb (dyadicTransposeSplitPlan q r b (2^b*W) hb)

/-- The quotient/remainder choice gives the exact requested exponent. -/
def dyadicTransposeExactPlan (a b W : ℕ) (hb : 0 < b) : DyadicTransposePlan a b W :=
  (show a/b*b+a%b = a by simpa only [Nat.mul_comm] using Nat.div_add_mod a b) ▸
    dyadicTransposeSplitPlan (a/b) (a%b) b W hb

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
