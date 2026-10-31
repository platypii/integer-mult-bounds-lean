module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalAdvanceControls

/-! The existing weight width covers every packed factory geometry operation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem weightWorkspaceWidth_packed_fits {P q w s t u band a b : ℕ}
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hab : a ≤ b) (hbs : b ≤ s) :
    let V := weightWorkspaceWidth P q w t u
    a+((b-a)+2*band)+s < 2^V ∧
      8*(t+1)^2+4*band+8 < 2^V ∧ w < 2^V ∧ b < 2^V ∧ b*w < 2^V := by
  let V := weightWorkspaceWidth P q w t u
  have hbig := (coefficientWorkspaceWidth_bound P (w+q+2) s t u 0 t hst.le).2.2.2.2.2.2.2
  change u*t*(t+1)^2*2^(13*P+8) < 2^V at hbig
  have hpow : 32 ≤ 2^(13*P+8) := (show 32 = 2^5 by decide).le.trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hmul := Nat.mul_le_mul_right ((t+1)^2)
    (Nat.mul_le_mul (show 1 ≤ u*t by nlinarith) hpow)
  have hwide : 8*(t+1)^2+4*band+8 < 2^V := by
    nlinarith only [hbig,hmul,hband,hst,hs]
  have hfit : a+((b-a)+2*band)+s < 2^V := by
    have hsub : a+(b-a) = b := Nat.add_sub_of_le hab
    nlinarith only [hwide,hsub,hbs,hband,hst,hs,Nat.zero_le (t*t)]
  have hb : b < 2^V := by nlinarith only [hwide,hbs,hst,Nat.zero_le (t*t)]
  have hsymbols := weightWorkspaceWidth_symbolVolume P q w s t u hst.le
  exact ⟨hfit,hwide,hsymbols.1,hb,(Nat.mul_le_mul_right w hbs).trans_lt hsymbols.2⟩
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
