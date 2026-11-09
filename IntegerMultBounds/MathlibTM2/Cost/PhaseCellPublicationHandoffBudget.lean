module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReverseCopyRows
import Mathlib.Tactic.Linarith

/-! The restoring core-order handoff is linear in ambient source traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem reverseCopyRowsCost_le_traffic (N R s L W : ℕ)
    (hrows : N*L ≤ s) (hL : 1 ≤ L) (hR : 1 ≤ R) (hW : 1 ≤ W) :
    reverseCopyRowsCost N (R*(L*W)) ≤ 35*(R*(s*W))+6 := by
  have hN : N ≤ s := (Nat.le_mul_of_pos_right N hL).trans hrows
  have htraffic : N ≤ R*(s*W) := hN.trans
    ((Nat.le_mul_of_pos_right s hW).trans (Nat.le_mul_of_pos_left _ hR))
  have hpayload : N*(R*(L*W)) ≤ R*(s*W) := by
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left (R*W) hrows
  unfold reverseCopyRowsCost
  nlinarith only [htraffic,hpayload]

end IntegerMultBounds.MathlibTM2.Cost
