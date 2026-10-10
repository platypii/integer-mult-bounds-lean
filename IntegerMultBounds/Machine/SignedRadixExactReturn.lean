import IntegerMultBounds.Machine.RadixSignedShiftRight
import IntegerMultBounds.Machine.ButterflyGuard
import IntegerMultBounds.Networks.GaussianBoundedArithmetic

/-! Exact native signed-field denominator lowering. A coarser semantic grid
supplies divisibility; word width alone never supplies normalization. -/
namespace IntegerMultBounds.Machine.SignedRadixExactReturn
noncomputable section
open RadixDigits ButterflySigned RadixSignedShiftRight
open Networks.GaussianPrecision

theorem value_append (xs ys : Word) :
    value (xs++ys)=value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih => simp [value,ih,pow_succ]; ring

private theorem last_value (xs : Word) (h : xs≠[]) :
    value xs=value xs.dropLast+2^(xs.length-1)*(xs.getLastD 0).val := by
  have hl : xs.getLastD 0=xs.getLast h := by rw [List.getLastD_eq_getLast?,List.getLast?_eq_some_getLast h]; rfl
  conv_lhs => rw [←List.dropLast_append_getLast h]
  rw [value_append,List.length_dropLast,hl]
  simp [value]

theorem signed_last (b : ℕ) (xs : Word) (hw : xs.length=b+1) :
    signedValue b xs=(value xs:ℤ)-(xs.getLastD 0).val*(2^(b+1):ℕ) := by
  have hn : xs≠[] := by intro h; simp [h] at hw
  have hv := last_value xs hn
  have ht := value_lt (by decide : 2≤2) xs.dropLast
  simp only [List.length_dropLast,hw,Nat.add_sub_cancel] at hv ht
  have hs := (xs.getLastD 0).isLt
  have hp : 2^(b+1)=2*2^b := by rw [pow_succ]; omega
  unfold signedValue
  rcases (show (xs.getLastD 0).val=0 ∨ (xs.getLastD 0).val=1 by omega) with h|h
  · have hb : value xs<2^b := by rw [h] at hv; omega
    simp only [ite_eq_left hb,h,Nat.cast_zero,zero_mul,sub_zero]
  · have hb : ¬value xs<2^b := by rw [h] at hv; omega
    simp only [ite_eq_right hb,h,Nat.cast_one,one_mul]

theorem signed_shift (b : ℕ) (x : Fin 2) (xs : Word) (hw : (x::xs).length=b+1) :
    signedValue b (x::xs)=(x.val:ℤ)+2*signedValue b (shifted (x::xs)) := by
  have hl : xs.length=b := by simp at hw; omega
  have ho := shifted_length (x::xs) (by simp)
  rw [signed_last b (x::xs) hw,signed_last b _ (ho.trans hw)]
  simp only [shifted,List.tail_cons,List.getLastD_cons,List.getLastD_concat,value_append]
  simp only [value,hl]
  have hp : (2^(b+1):ℕ)=2*2^b := by rw [pow_succ]; omega
  rw [hp]
  push_cast
  ring

/-- The least significant native digit is zero exactly when the signed
numerator is divisible by two. Arithmetic shift then divides it exactly. -/
theorem signed_shift_even (b : ℕ) (x : Fin 2) (xs : Word)
    (hw : (x::xs).length=b+1) (he : (2:ℤ)∣signedValue b (x::xs)) :
    signedValue b (x::xs)=2*signedValue b (shifted (x::xs)) := by
  have hs := signed_shift b x xs hw
  obtain ⟨k,hk⟩ := he
  have hx := x.isLt
  have hz : x.val=0 := by omega
  simpa [hz] using hs

theorem complex_raise (a b : ℤ) (n d : ℕ) :
    complexValue (a*2^d) (b*2^d) (n+d)=complexValue a b n := by
  unfold complexValue
  push_cast
  rw [pow_add]
  have hn : (2:ℂ)^n≠0 := pow_ne_zero _ (by norm_num)
  have hd : (2:ℂ)^d≠0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- Coarser-grid membership forces literal divisibility of both stored
numerators, independent of their signed record width. -/
theorem coarser_divisibility (a b : ℤ) (n d M : ℕ)
    (h : BoundedGrid n M (complexValue a b (n+d))) :
    (2^d:ℤ)∣a ∧ (2^d:ℤ)∣b := by
  obtain ⟨c,e,hce,_,_⟩ := h
  have hn : (2:ℂ)^n≠0 := pow_ne_zero _ (by norm_num)
  have hv : complexValue a b (n+d)=complexValue c e n := by
    exact (eq_div_iff hn).mpr hce
  rw [←complex_raise c e n d] at hv
  obtain ⟨ha,hb⟩ := ButterflyGuard.numerators_unique a b (c*2^d) (e*2^d) (n+d) hv
  exact ⟨⟨c,by rw [ha]; ring⟩,⟨e,by rw [hb]; ring⟩⟩

/-- Actual sign-extended output fields at exponent n decode exactly as the
input fields at exponent n+1, when the returned coefficient is on grid n. -/
theorem exact_return (b n M : ℕ) (xr xi : Fin 2) (rs is : Word)
    (hr : (xr::rs).length=b+1) (hi : (xi::is).length=b+1)
    (hg : BoundedGrid n M (complexValue (signedValue b (xr::rs))
      (signedValue b (xi::is)) (n+1))) :
    complexValue (signedValue b (shifted (xr::rs)))
      (signedValue b (shifted (xi::is))) n =
    complexValue (signedValue b (xr::rs)) (signedValue b (xi::is)) (n+1) := by
  have hd := coarser_divisibility _ _ n 1 M hg
  simp only [pow_one] at hd
  rw [signed_shift_even b xr rs hr hd.1,signed_shift_even b xi is hi hd.2]
  simpa only [pow_one,mul_comm (2:ℤ)] using
    (complex_raise (signedValue b (shifted (xr::rs)))
      (signedValue b (shifted (xi::is))) n 1).symm

/-- Restore any certified coarser exponent by repeated exact shifts; all
intermediate words keep the same signed field width. -/
theorem exact_return_iterate (b n d M : ℕ) (rs is : Word)
    (hr : rs.length=b+1) (hi : is.length=b+1)
    (hg : BoundedGrid n M (complexValue (signedValue b rs)
      (signedValue b is) (n+d))) :
    ((shifted^[d]) rs).length=b+1 ∧ ((shifted^[d]) is).length=b+1 ∧
    complexValue (signedValue b ((shifted^[d]) rs))
      (signedValue b ((shifted^[d]) is)) n =
    complexValue (signedValue b rs) (signedValue b is) (n+d) := by
  induction d generalizing rs is with
  | zero => simp [hr,hi]
  | succ d ih =>
    cases rs with
    | nil => simp at hr
    | cons xr rs =>
      cases is with
      | nil => simp at hi
      | cons xi is =>
        have hraise := bounded_raise hg d
        have he := exact_return b (n+d) (M*2^d) xr xi rs is hr hi
          (by simpa only [Nat.add_assoc] using hraise)
        have hgr : BoundedGrid n M (complexValue (signedValue b (shifted (xr::rs)))
            (signedValue b (shifted (xi::is))) (n+d)) := by
          rw [he]
          simpa only [Nat.add_assoc] using hg
        have hrl := (shifted_length (xr::rs) (by simp)).trans hr
        have hil := (shifted_length (xi::is) (by simp)).trans hi
        obtain ⟨hro,hio,heo⟩ := ih _ _ hrl hil hgr
        rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
        exact ⟨hro,hio,by rw [heo,he]; simp only [Nat.add_assoc]⟩

end
end IntegerMultBounds.Machine.SignedRadixExactReturn
