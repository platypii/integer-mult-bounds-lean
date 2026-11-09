module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReverseCopyRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveWidthSetup
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

/-- Generating and retiring the two row-width products is ambient-linear too. -/
theorem archiveWidthSetupCosts_le_traffic (R s L W : ℕ)
    (hL : 1 ≤ L) (hfit : L ≤ s) (hR : 1 ≤ R) (hW : 1 ≤ W) :
    archiveWidthSetupCost R L W+2*(L*W+R*(L*W))+5 ≤ 80*(R*(s*W)) ∧
      2*archiveWidthSetupCost R L W ≤ 80*(R*(s*W)) := by
  have hpacket : L*W ≤ R*(s*W) :=
    (Nat.mul_le_mul_right W hfit).trans (Nat.le_mul_of_pos_left _ hR)
  have hvolume : R*(L*W) ≤ R*(s*W) := Nat.mul_le_mul_left R (Nat.mul_le_mul_right W hfit)
  have hcore : L ≤ R*(s*W) := (Nat.le_mul_of_pos_right L hW).trans hpacket
  have hs : 1 ≤ s*W := Nat.mul_le_mul (hL.trans hfit) hW
  have hreplicas : R ≤ R*(s*W) := Nat.le_mul_of_pos_right R hs
  have hone : 1 ≤ R*(s*W) := Nat.mul_le_mul hR hs
  unfold archiveWidthSetupCost
  constructor <;> nlinarith only [hpacket,hvolume,hcore,hreplicas,hone]

end IntegerMultBounds.MathlibTM2.Cost
