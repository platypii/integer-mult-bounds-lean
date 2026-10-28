module

public import IntegerMultBounds.MathlibTM2.Node.TopWord

/-! Linear time for one final rounding pass, uniformly in the chosen shift. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Node

theorem topShiftWordCost_eq {w d k : ℕ} (hsize : d+k ≤ w) :
    topShiftWordCost w d k = 12*w+22 := by
  unfold topShiftWordCost
  omega

theorem finalRound_pass_cost_le {w d k : ℕ} (hsize : d+k ≤ w) (s : ℕ) :
    1+(s*(topShiftWordCost w d k+1)+1)+(2*(s*k)+2) ≤ s*(14*w+23)+4 := by
  rw [topShiftWordCost_eq hsize]
  have hk : k ≤ w := by omega
  have hmul := Nat.mul_le_mul_left (2*s) hk
  nlinarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
