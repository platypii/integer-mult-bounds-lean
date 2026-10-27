module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPacking

/-! A positive power of two has one real pair bit in its fixed-width word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem csyms_pow_two (A w e : ℕ) (he : e < w) :
    csyms A w (⟨(2 : ℤ)^e,0⟩ : GaussianInt) =
      List.replicate e (pairSym A false false)++
        pairSym A true false::List.replicate (w-e-1) (pairSym A false false) := by
  have hpow : (2 : ℕ)^e < 2^w := Nat.pow_lt_pow_right (by decide) he
  have hv : ((2 : ZMod (2^w))^e).val = (2 : ℕ)^e := by
    have hc : ((2 : ZMod (2^w))^e) = ((2^e : ℕ) : ZMod (2^w)) := by norm_cast
    rw [hc,ZMod.val_cast_of_lt hpow]
  apply List.ext_getElem (by simp [csyms,coeffSyms]; omega)
  intro i hi hj
  simp only [csyms,coeffSyms,List.getElem_ofFn,red,Int.cast_pow,Int.cast_ofNat,hv,ZMod.val_zero,Nat.zero_testBit]
  by_cases hie : i < e
  · have hne : e ≠ i := by omega
    simp [List.getElem_append,hie,Nat.testBit_two_pow,hne]
  by_cases heq : i = e
  · subst i
    simp [List.getElem_append,Nat.testBit_two_pow]
  · have hne : e ≠ i := by omega
    cases hsub : i-e with
    | zero => omega
    | succ j => simp [List.getElem_append,hie,hsub,Nat.testBit_two_pow,hne]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
