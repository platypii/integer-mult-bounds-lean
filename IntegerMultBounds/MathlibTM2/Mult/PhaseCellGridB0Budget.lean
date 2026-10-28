module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedB0Budget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundDimensionSelection

/-! The actual normalized complex error meets the same smallness gate at a linear target. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem gridInverse_normalized_smallness {p target j : ℕ} (hp : 4 ≤ p) (htarget : p+8 ≤ target) :
    (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j)+
      (32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2 ≤ 1/2 := by
  have hs := executedInverse_normalized_smallness hp
  have hd : (1/(2 : ℝ)^target)/(2 : ℝ)^j ≤ 1/(2 : ℝ)^target :=
    div_le_self (by positivity) (one_le_pow₀ (by norm_num))
  have ht : 1/(2 : ℝ)^target ≤ 1/(2 : ℝ)^(p+8) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) htarget
  have hpos : (0 : ℝ) ≤ 1/2^(p+8) := by positivity
  linarith only [hs,hd,ht,hpos]

theorem gridInverse_operator_error_le_ten {p target j : ℕ} (hp : 4 ≤ p) (htarget : p+8 ≤ target) :
    7+(2 : ℝ)^p*((2/2^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j)+
      (32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2) ≤ 10 := by
  have hd : (1/(2 : ℝ)^target)/(2 : ℝ)^j ≤ 1/(2 : ℝ)^target :=
    div_le_self (by positivity) (one_le_pow₀ (by norm_num))
  have ht : 1/(2 : ℝ)^target ≤ 1/(2 : ℝ)^(p+8) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) htarget
  have hs := mul_le_mul_of_nonneg_left (hd.trans ht) (by positivity : (0 : ℝ) ≤ 2^p)
  have hcancel : (2 : ℝ)^p*(1/(2 : ℝ)^(p+8)) = 1/256 := by
    rw [pow_add]
    norm_num
    field_simp
  rw [hcancel] at hs
  have hpPow : (p : ℝ) ≤ (2 : ℝ)^p := by exact_mod_cast (show p < 2^p from Nat.lt_two_pow_self).le
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg p) hpPow 2
  have hden : 64*(p : ℝ)^2*(2 : ℝ)^p ≤ (2 : ℝ)^(45*p) := by
    calc
      _ ≤ 64*((2 : ℝ)^p)^2*(2 : ℝ)^p := by gcongr
      _ = (2 : ℝ)^(p*3+6) := by rw [pow_add,pow_mul]; norm_num; ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hm : (2 : ℝ)^p*((32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2) ≤ 1/4 := by
    have he : (2 : ℝ)^p*((32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2) =
        (16*(p : ℝ)^2*(2 : ℝ)^p)/(2 : ℝ)^(45*p) := by ring
    rw [he]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^(45*p))).mpr
    nlinarith only [hden]
  have hr : (2 : ℝ)^p*(2/(2 : ℝ)^p) = 2 := by field_simp
  nlinarith only [hs,hm,hr]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
