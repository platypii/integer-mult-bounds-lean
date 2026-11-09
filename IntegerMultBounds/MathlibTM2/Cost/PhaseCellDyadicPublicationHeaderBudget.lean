module

public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

/-! Binary dimension generation and retirement fit in linear source traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

theorem dyadicPublicationHeaderCosts_le (N b s L W V p cV : ℕ)
    (hrows : N*L ≤ s) (hL : 1 ≤ L) (hspan : L ≤ s) (hW : 1 ≤ W)
    (hp : 1 ≤ p) (hps : p ≤ s) (hV : V ≤ cV*p) :
    let bill := 21*(Nat.clog 2 N+b+L*W)+36*V+85
    bill+6*V+7 ≤ (400+100*cV)*(2^b*(s*W)) ∧
    2*bill ≤ (400+100*cV)*(2^b*(s*W)) := by
  dsimp only
  let traffic := 2^b*(s*W)
  have hreplicas : 1 ≤ 2^b := Nat.two_pow_pos b
  have hvolume : 1 ≤ traffic := Nat.mul_pos hreplicas (Nat.mul_pos (hp.trans hps) hW)
  have hs : s ≤ traffic := (Nat.le_mul_of_pos_right s hW).trans (Nat.le_mul_of_pos_left _ hreplicas)
  have hN : N ≤ s := (Nat.le_mul_of_pos_right N hL).trans hrows
  have ha : Nat.clog 2 N ≤ traffic :=
    (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le : N ≤ 2^N)).trans (hN.trans hs)
  have hb : b ≤ traffic := Nat.lt_two_pow_self.le.trans
    (Nat.le_mul_of_pos_right (2^b) (Nat.mul_pos (hp.trans hps) hW))
  have hpacket : L*W ≤ traffic := (Nat.mul_le_mul_right W hspan).trans
    (Nat.le_mul_of_pos_left _ hreplicas)
  have hV' : V ≤ cV*traffic := hV.trans (Nat.mul_le_mul_left cV (hps.trans hs))
  change _ ≤ (400+100*cV)*traffic ∧ _ ≤ (400+100*cV)*traffic
  constructor <;> nlinarith only [ha,hb,hpacket,hV',hvolume]

end IntegerMultBounds.MathlibTM2.Cost
