import IntegerMultBounds.Machine.SignedRadixExactReturn

/-! Literal constant-width promotion of a native signed numerator to a finer
common denominator. Low zero digits are prepended and high digits truncated;
a real signed capacity guard proves exact multiplication rather than wrapping. -/
namespace IntegerMultBounds.Machine.NativeSignedGapPromoteWord
noncomputable section
open RadixSignedShiftRight (Word)
open RadixDigits (value)
open ButterflySigned (signedValue complexValue)

/-- The native fields are least-significant digit first. Promotion by d moves
every retained digit d places to the right within the unchanged field width. -/
def result (d : ℕ) (xs : Word) := List.replicate (min d xs.length) 0++xs.take (xs.length-d)

theorem result_length (d : ℕ) (xs : Word) : (result d xs).length=xs.length := by
  simp only [result,List.length_append,List.length_replicate,List.length_take]
  omega

private theorem zeros_value (d : ℕ) : value (List.replicate d (0 : Fin 2))=0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [List.replicate_succ,value,Fin.val_zero,ih,Nat.mul_zero,Nat.add_zero]

/-- Actual literal word promotion has the multiplied source residue modulo the
original field width. There is no executable multiplication premise. -/
theorem result_residue (d : ℕ) (xs : Word) (hd : d≤xs.length) :
    (value (result d xs) : ZMod (2^xs.length))=
      (2^d : ZMod (2^xs.length))*(value xs : ZMod (2^xs.length)) := by
  let lo := xs.take (xs.length-d)
  let hi := xs.drop (xs.length-d)
  have hlo : lo.length=xs.length-d := by simp only [lo,List.length_take]; omega
  have hxs : value xs=value lo+2^(xs.length-d)*value hi := by
    have h := SignedRadixExactReturn.value_append lo hi
    rw [show lo++hi=xs by exact List.take_append_drop _ _,hlo] at h
    exact h
  have hr : value (result d xs)=2^d*value lo := by
    simp only [result,min_eq_left hd,SignedRadixExactReturn.value_append,zeros_value,
      List.length_replicate,Nat.zero_add,lo]
  have hp : 2^d*2^(xs.length-d)=2^xs.length := by rw [←pow_add]; congr 1; omega
  have he : 2^d*value xs=value (result d xs)+2^xs.length*value hi := by
    rw [hxs,hr,Nat.mul_add,←Nat.mul_assoc,hp]
  have hz := congrArg (fun t : ℕ => (t : ZMod (2^xs.length))) he
  have hmod : (2 : ZMod (2^xs.length))^xs.length=0 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using ZMod.natCast_self (2^xs.length)
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,hmod,zero_mul,add_zero] at hz
  exact hz.symm

/-- Exact signed multiplication under the actual multiplied-numerator capacity
bound used by native spectator alignment. -/
theorem result_signed_bounded (b d M : ℕ) (xs : Word) (hw : xs.length=b+1) (hd : d≤xs.length)
    (hb : |signedValue b xs|≤(M:ℤ)) (hguard : M*2^d<2^b) :
    signedValue b (result d xs)=signedValue b xs*2^d := by
  have ha := abs_le.mp hb
  have hpos : (0:ℤ)≤2^d := by positivity
  have hbound : (M:ℤ)*2^d<((2^b:ℕ):ℤ) := by exact_mod_cast hguard
  apply ButterflySigned.signed_unique b _ ((result_length d xs).trans hw) (signedValue b xs*2^d)
  · constructor
    · have hm := mul_le_mul_of_nonneg_right ha.1 hpos
      rw [neg_mul] at hm
      omega
    · have hm := mul_le_mul_of_nonneg_right ha.2 hpos
      omega
  · have hr := result_residue d xs hd
    rw [hw] at hr
    rw [hr]
    push_cast
    rw [ButterflySigned.signed_cast,mul_comm]

/-- A genuine bounded-numerator reserve implies literal signed multiplication
inside the original field. Width alone never licenses an overflowing shift. -/
theorem result_signed (b p d : ℕ) (xs : Word) (hw : xs.length=b+1) (hd : d≤xs.length)
    (hb : |signedValue b xs|≤((2^p:ℕ):ℤ)) (hguard : p+d<b) :
    signedValue b (result d xs)=signedValue b xs*2^d := by
  have ha := abs_le.mp hb
  have hp : ((2^p:ℕ):ℤ)*(2^d:ℤ)=((2^(p+d):ℕ):ℤ) := by push_cast; rw [pow_add]
  have hpos : (0:ℤ)≤2^d := by positivity
  have hbound : ((2^(p+d):ℕ):ℤ)<((2^b:ℕ):ℤ) := by exact_mod_cast Nat.pow_lt_pow_right (by decide : 1<2) hguard
  apply ButterflySigned.signed_unique b _ ((result_length d xs).trans hw) (signedValue b xs*2^d)
  · constructor
    · have hm := mul_le_mul_of_nonneg_right ha.1 hpos
      rw [neg_mul,hp] at hm
      omega
    · have hm := mul_le_mul_of_nonneg_right ha.2 hpos
      rw [hp] at hm
      omega
  · have hr := result_residue d xs hd
    rw [hw] at hr
    rw [hr]
    push_cast
    rw [ButterflySigned.signed_cast,mul_comm]

/-- Promoting both fields and the true common denominator keeps the original
Gaussian coefficient exactly, with unchanged literal real/imaginary widths. -/
theorem gaussian_exact (b p n d : ℕ) (re im : Word)
    (hr : re.length=b+1) (hi : im.length=b+1) (hd : d≤b+1)
    (hbr : |signedValue b re|≤((2^p:ℕ):ℤ)) (hbi : |signedValue b im|≤((2^p:ℕ):ℤ))
    (hguard : p+d<b) :
    (result d re).length=b+1 ∧ (result d im).length=b+1 ∧
      complexValue (signedValue b (result d re)) (signedValue b (result d im)) (n+d)=
        complexValue (signedValue b re) (signedValue b im) n := by
  rw [result_signed b p d re hr (hr.symm ▸ hd) hbr hguard,
    result_signed b p d im hi (hi.symm ▸ hd) hbi hguard]
  exact ⟨(result_length d re).trans hr,(result_length d im).trans hi,
    SignedRadixExactReturn.complex_raise _ _ n d⟩

end
end IntegerMultBounds.Machine.NativeSignedGapPromoteWord
