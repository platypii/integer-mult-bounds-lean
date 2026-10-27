module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPacking

/-! The scaled negative unit is a zero prefix followed by sign-extension bits. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem csyms_negative_one (A w : ℕ) :
    csyms A w (⟨-1,0⟩ : GaussianInt) = List.replicate w (pairSym A true false) := by
  have hpow : 1 ≤ 2^w := Nat.one_le_pow w 2 (by decide)
  have hval : (-1 : ZMod (2^w)).val = 2^w-1 := by
    have hh := ZMod.val_neg_one (2^w-1)
    have he : (2^w-1).succ = 2^w := by omega
    rw [he] at hh
    exact hh
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hiw : i < w := by simpa using hi'
  simp [csyms,coeffSyms,red,hval]

theorem csyms_negative_power_two (A w q : ℕ) (hq : q ≤ w) :
    csyms A w (⟨-(2 : ℤ)^q,0⟩ : GaussianInt) =
      List.replicate q (pairSym A false false)++List.replicate (w-q) (pairSym A true false) := by
  have hcast : (2 : ZMod (2^q))^q = 0 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using ZMod.natCast_self (2^q)
  have hlow : csyms A q (⟨-(2 : ℤ)^q,0⟩ : GaussianInt) = csyms A q 0 := by
    simp [csyms,red,hcast]
  have hhigh : (⟨(-(2 : ℤ)^q)/(2 : ℤ)^q,(0 : ℤ)/(2 : ℤ)^q⟩ : GaussianInt) = ⟨-1,0⟩ := by
    simp [show (2 : ℤ)^q ≠ 0 by positivity]
  have hh := csyms_floor_div_append A q (w-q) (⟨-(2 : ℤ)^q,0⟩ : GaussianInt)
  rw [show q+(w-q) = w by omega,hlow,hhigh,csyms_negative_one] at hh
  simpa only [csyms_zero] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
