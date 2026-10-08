import IntegerMultBounds.Machine.FixedMul
import IntegerMultBounds.Compact.PowerTwoDigits

/-! The signed fixed-point multiply computes the product truncated toward
zero by `p` bits: for two's complement words of width `w ≥ p + 2` whose
signed values have magnitude at most `2^p`, the result word's signed value is
`(x * y).tdiv 2^p`, the fixed-point rounding `ρ` of the numerical maps. -/

namespace IntegerMultBounds.Machine.FixedMul

open Counter (value)
open TwosComplement (signed negWord signed_negWord signed_bounds signed_emod)
open Gather (field)
open IntegerMultBounds.Compact.PowerTwo (field_take value_take_add_drop field_append_right)

section Field

theorem value_field_prefix (cs : List Bool) (d : ℕ) (hd : d ≤ cs.length) :
    value (field cs 0 d) = value cs % 2 ^ d := by
  rw [field_take cs d hd, value_take_add_drop cs d, List.length_take, min_eq_left hd]
  have := Counter.value_lt (cs.take d)
  rw [List.length_take, min_eq_left hd] at this
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this]

theorem value_field_middle (cs : List Bool) (m d : ℕ) (h : m + d ≤ cs.length) :
    value (field cs m d) = value cs / 2 ^ m % 2 ^ d := by
  have hsplit := value_take_add_drop cs m
  rw [List.length_take, min_eq_left (by omega)] at hsplit
  have hlt := Counter.value_lt (cs.take m)
  rw [List.length_take, min_eq_left (by omega)] at hlt
  have hdiv : value cs / 2 ^ m = value (cs.drop m) := by
    rw [hsplit, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
  rw [hdiv, ← value_field_prefix (cs.drop m) d (by rw [List.length_drop]; omega)]
  congr 1
  have := field_append_right (cs.take m) (cs.drop m) 0 d
  rw [List.take_append_drop, List.length_take, min_eq_left (by omega), add_zero] at this
  exact this

end Field

section Signs

/-- The top bit is the sign. -/
theorem top_eq_false_iff (x : List Bool) (hx : x ≠ []) : x.getLastD false = false ↔ 0 ≤ signed x := by
  have hv : (0 : ℤ) ≤ value x := by positivity
  have hlt : (value x : ℤ) < 2 ^ x.length := by exact_mod_cast Counter.value_lt x
  have hpow : (2 : ℤ) ^ x.length = 2 * 2 ^ (x.length - 1) := by
    rw [← pow_succ']; congr 1; have := List.length_pos_of_ne_nil hx; omega
  have hd := TwosComplement.value_dropLast x hx
  have hdl : (value x.dropLast : ℤ) < 2 ^ (x.length - 1) := by
    exact_mod_cast TwosComplement.value_dropLast_lt x hx
  unfold signed
  rw [TwosComplement.getLastD_eq x hx]
  cases hb : x.getLast hx
  · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, true_iff]; exact hv
  · simp only [↓reduceIte, Bool.true_eq_false, false_iff, not_le]
    rw [hb] at hd
    simp only [BinaryAdd.bitValue, ↓reduceIte, mul_one] at hd
    have : (value x : ℤ) = value x.dropLast + 2 ^ (x.length - 1) := by exact_mod_cast hd
    linarith

/-- The magnitude word has the absolute value, when the value is not the
most negative one. -/
theorem value_mag (x : List Bool) (hx : x ≠ []) (h : signed x ≠ -(2 : ℤ) ^ (x.length - 1)) :
    (value (mag x) : ℤ) = |signed x| := by
  unfold mag
  cases hb : x.getLastD false
  · have h0 : 0 ≤ signed x := (top_eq_false_iff x hx).mp hb
    rw [abs_of_nonneg h0]
    unfold signed; rw [hb]; simp
  · have h0 : ¬ 0 ≤ signed x := fun hc => by
      have := (top_eq_false_iff x hx).mpr hc; rw [hb] at this; exact Bool.noConfusion this
    have hne : negWord x ≠ [] := by
      intro h0; have := TwosComplement.negWord_length x; rw [h0] at this
      exact hx (List.length_eq_zero_iff.mp this.symm)
    have hnn : 0 ≤ signed (negWord x) := by rw [signed_negWord x hx h]; omega
    have htop := (top_eq_false_iff _ hne).mpr hnn
    rw [abs_of_neg (by omega), ← signed_negWord x hx h]
    simp only [↓reduceIte]
    unfold signed
    rw [htop]
    simp

end Signs

section Result

variable (x y : List Bool) (p w : ℕ) (hx : x.length = w) (hy : y.length = w) (hw : p + 2 ≤ w)
  (hxb : |signed x| ≤ 2 ^ p) (hyb : |signed y| ≤ 2 ^ p)

include hx hw hxb in
theorem x_ne_min : signed x ≠ -(2 : ℤ) ^ (x.length - 1) := by
  intro h
  have h1 : (2 : ℤ) ^ p < 2 ^ (x.length - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  rw [h, abs_neg, abs_pow, abs_two] at hxb
  linarith

include hx hy hw hxb hyb in
/-- The padded product has the absolute value of the product. -/
theorem value_padProd : (value (padProd x y w) : ℤ) = |signed x * signed y| := by
  have hx0 : x ≠ [] := by intro h0; rw [h0] at hx; simp at hx; omega
  have hy0 : y ≠ [] := by intro h0; rw [h0] at hy; simp at hy; omega
  unfold padProd
  rw [TwosComplement.value_append, TwosComplement.value_replicate_false, mul_zero, add_zero,
    BinaryMultiply.horner_value, abs_mul]
  push_cast
  rw [value_mag x hx0 (x_ne_min x p w hx hw hxb), value_mag y hy0 (x_ne_min y p w hy hw hyb)]

include hx hy in
theorem padProd_length : (padProd x y w).length = 2 * w := by
  have := BinaryMultiply.horner_length (mag x) (mag y)
  rw [mag_length, mag_length, hx, hy] at this
  simp [padProd]; omega

include hx hy hw hxb hyb in
/-- The field read from the padded product is the truncated magnitude. -/
theorem value_field_result :
    (value (field (padProd x y w) p w) : ℤ) = |signed x * signed y| / 2 ^ p := by
  have hlen := padProd_length x y w hx hy
  rw [value_field_middle _ _ _ (by omega)]
  have hv := value_padProd x y p w hx hy hw hxb hyb
  have hbound : |signed x * signed y| / 2 ^ p < 2 ^ w := by
    have h1 : |signed x * signed y| ≤ 2 ^ p * 2 ^ p := by
      rw [abs_mul]; exact mul_le_mul hxb hyb (abs_nonneg _) (by positivity)
    have h2 : (2 : ℤ) ^ p * 2 ^ p / 2 ^ p = 2 ^ p := by
      rw [Int.mul_ediv_cancel _ (by positivity)]
    have h3 : (2 : ℤ) ^ p < 2 ^ w := pow_lt_pow_right₀ (by norm_num) (by omega)
    calc |signed x * signed y| / 2 ^ p ≤ 2 ^ p * 2 ^ p / 2 ^ p :=
          Int.ediv_le_ediv (by positivity) h1
      _ < 2 ^ w := by rw [h2]; exact h3
  have hnat : (value (padProd x y w) / 2 ^ p % 2 ^ w : ℕ) = value (padProd x y w) / 2 ^ p := by
    apply Nat.mod_eq_of_lt
    have : ((value (padProd x y w) / 2 ^ p : ℕ) : ℤ) < 2 ^ w := by
      push_cast; rw [hv]; exact hbound
    exact_mod_cast this
  rw [hnat]; push_cast; rw [hv]

include hx hy hw hxb hyb in
/-- The result word's signed value is the product truncated toward zero. -/
theorem signed_result : signed (result x y p w) = (signed x * signed y).tdiv (2 ^ p) := by
  have hx0 : x ≠ [] := by intro h0; rw [h0] at hx; simp at hx; omega
  have hy0 : y ≠ [] := by intro h0; rw [h0] at hy; simp at hy; omega
  have hfl : (field (padProd x y w) p w).length = w := Gather.field_length _ _ _
  have hfne : field (padProd x y w) p w ≠ [] := by
    intro h0; rw [h0] at hfl; simp at hfl; omega
  have hfv := value_field_result x y p w hx hy hw hxb hyb
  -- the field's signed value is its (nonnegative) value
  have hsmall : (value (field (padProd x y w) p w) : ℤ) < 2 ^ (w - 1) := by
    rw [hfv]
    have h1 : |signed x * signed y| ≤ 2 ^ p * 2 ^ p := by
      rw [abs_mul]; exact mul_le_mul hxb hyb (abs_nonneg _) (by positivity)
    have h2 : (2 : ℤ) ^ p * 2 ^ p / 2 ^ p = 2 ^ p := by
      rw [Int.mul_ediv_cancel _ (by positivity)]
    have h3 : (2 : ℤ) ^ p < 2 ^ (w - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
    calc |signed x * signed y| / 2 ^ p ≤ 2 ^ p * 2 ^ p / 2 ^ p :=
          Int.ediv_le_ediv (by positivity) h1
      _ < 2 ^ (w - 1) := by rw [h2]; exact h3
  have hfs : signed (field (padProd x y w) p w) = value (field (padProd x y w) p w) := by
    unfold signed
    split_ifs with htop
    · exfalso
      have hd := TwosComplement.value_dropLast _ hfne
      rw [← TwosComplement.getLastD_eq _ hfne, htop] at hd
      simp only [BinaryAdd.bitValue, ↓reduceIte, mul_one, hfl] at hd
      have : (value (field (padProd x y w) p w) : ℤ) =
          value (field (padProd x y w) p w).dropLast + 2 ^ (w - 1) := by exact_mod_cast hd
      have h0 : (0 : ℤ) ≤ value (field (padProd x y w) p w).dropLast := by positivity
      linarith
    · simp
  have hfs' : signed (field (padProd x y w) p w) = |signed x * signed y| / 2 ^ p := by rw [hfs, hfv]
  have hne : signed (field (padProd x y w) p w) ≠ -(2 : ℤ) ^ ((field (padProd x y w) p w).length - 1) := by
    rw [hfs', hfl]; have : (0 : ℤ) ≤ |signed x * signed y| / 2 ^ p := by positivity
    have : (0 : ℤ) < 2 ^ (w - 1) := by positivity
    omega
  unfold result
  have hsx := top_eq_false_iff x hx0
  have hsy := top_eq_false_iff y hy0
  cases hbx : x.getLastD false <;> cases hby : y.getLastD false <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;>
    rw [hbx] at hsx <;> rw [hby] at hsy
  · -- both nonnegative
    have h1 : 0 ≤ signed x := hsx.mp rfl
    have h2 : 0 ≤ signed y := hsy.mp rfl
    rw [hfs', abs_of_nonneg (mul_nonneg h1 h2), Int.tdiv_eq_ediv_of_nonneg (mul_nonneg h1 h2)]
  · have h1 : 0 ≤ signed x := hsx.mp rfl
    have h2 : signed y < 0 := lt_of_not_ge (fun hc => Bool.noConfusion (hsy.mpr hc))
    rw [signed_negWord _ hfne hne, hfs', abs_of_nonpos (by nlinarith)]
    have hP : signed x * signed y = -(-(signed x * signed y)) := (neg_neg _).symm
    conv_rhs => rw [hP, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by nlinarith)]
  · have h1 : signed x < 0 := lt_of_not_ge (fun hc => Bool.noConfusion (hsx.mpr hc))
    have h2 : 0 ≤ signed y := hsy.mp rfl
    rw [signed_negWord _ hfne hne, hfs', abs_of_nonpos (by nlinarith)]
    have hP : signed x * signed y = -(-(signed x * signed y)) := (neg_neg _).symm
    conv_rhs => rw [hP, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by nlinarith)]
  · have h1 : signed x < 0 := lt_of_not_ge (fun hc => Bool.noConfusion (hsx.mpr hc))
    have h2 : signed y < 0 := lt_of_not_ge (fun hc => Bool.noConfusion (hsy.mpr hc))
    rw [hfs', abs_of_nonneg (by nlinarith), Int.tdiv_eq_ediv_of_nonneg (by nlinarith)]

end Result

end IntegerMultBounds.Machine.FixedMul
