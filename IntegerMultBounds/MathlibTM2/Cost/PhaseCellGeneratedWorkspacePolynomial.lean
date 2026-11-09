module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Cost.MatchBandLoad
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! Shared setup is cubic in encoded precision and linear in ambient header traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem generatedBatchSetupBudget_poly
    (C P N q s t u band l L Z : ℕ) (hZ : 1 ≤ Z)
    (hP : P ≤ Z) (hN : N ≤ Z) (hq : q ≤ Z) (hl : l ≤ Z) (hL : L ≤ Z)
    (hW : integerSetupWidth P q (N+1) 0 ≤ Z)
    (hV : coefficientWorkspaceWidth P (integerSetupWidth P q (N+1) 0) t u band L ≤ Z)
    (hT : weightWorkspaceWidth P q (2*q+8) t u ≤ Z) :
    generatedBatchSetupBudget C P N q s t u band l L ≤
      288*C*(ssMulConst+1)*Z^3+100000000*(C+1)*(Z+1)^3+
        1000000*(s+t+u+band+1)*(Z+1) := by
  have hmul := band_rmul_le hW hZ
  have hsize : (2*integerSetupWidth P q (N+1) 0).size ≤ 2*Z := by
    have h := Nat.size_le.mpr (Nat.lt_two_pow_self (n := 2*integerSetupWidth P q (N+1) 0))
    omega
  unfold generatedBatchSetupBudget
  dsimp only
  calc
    _ ≤ C*(288*(ssMulConst+1)*Z^3)+60300*(2*Z+1)*(Z+1)^2+
        100000*(Z+Z+1)^2+
        100000*(Z*Z+Z+Z+Z+s+t+u+band+Z+Z+1)*(Z+Z+Z+1)+
        100000*(C+1)*(Z+1)^2*(Z+Z+1) := by gcongr
    _ ≤ _ := by ring_nf; omega

end IntegerMultBounds.MathlibTM2.Cost
