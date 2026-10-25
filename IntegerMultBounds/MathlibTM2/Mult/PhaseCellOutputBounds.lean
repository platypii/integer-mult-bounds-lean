module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarRange

/-! # Range and accuracy of the final executed similarity multiplication

The interior scalar numerator has norm at most four. Its exact power-of-two
rescaling and multiplication by a generated weight word have concrete signed
word bounds. The weight's encoding error is charged at the rescaled magnitude.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

/-- The actual truncated scalar product preserves the proved magnitude four. -/
theorem scalar_product_norm (q : ℕ) (x a : GaussianInt)
    (hx : ‖value q x‖ ≤ 2) (ha : ‖value q a‖ ≤ 2) :
    ‖value q (tdivN q (x * a))‖ ≤ 4 := by
  have h := normalized_product_norm q 0 1 1 x a (by simpa using hx) (by simpa using ha)
  norm_num at h
  exact h

theorem scalar_products_norm (q : ℕ) (xs : List GaussianInt) (a : GaussianInt)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 2) (ha : ‖value q a‖ ≤ 2) :
    ∀ z ∈ xs.map (fun x => tdivN q (x * a)), ‖value q z‖ ≤ 4 := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  exact scalar_product_norm q x a (hxs x hx) ha

/-- Exact numerator rescaling restores the magnitude of a cell output. -/
theorem scaled_output_norm (q d : ℕ) (z : GaussianInt) (hz : ‖value q z‖ ≤ 4) :
    ‖value q ((2 : GaussianInt) ^ d * z)‖ ≤ (2 : ℝ) ^ (d + 2) := by
  rw [value_pow_two_mul, norm_mul, norm_pow, Complex.norm_ofNat]
  calc
    _ ≤ (2 : ℝ) ^ d * 4 := mul_le_mul_of_nonneg_left hz (by positivity)
    _ = _ := by rw [pow_add]; norm_num

theorem scaled_output_fits {q d w : ℕ} (hw : q + d + 4 ≤ w) (z : GaussianInt)
    (hz : ‖value q z‖ ≤ 4) : Fits w ((2 : GaussianInt) ^ d * z) :=
  fits_of_value_power (by omega) _ (scaled_output_norm q d z hz)

/-- Encoding a nonnegative similarity weight does not increase its norm. -/
theorem output_weight_norm (q : ℕ) (a : ℚ) (ha0 : 0 ≤ (a : ℝ)) (ha1 : (a : ℝ) ≤ 1) :
    ‖value q (rationalWord q a)‖ ≤ 1 := by
  have haQ : 0 ≤ a := by exact_mod_cast ha0
  rw [rationalWord_norm, abs_of_nonneg (rationalWord_nonneg q a haQ)]
  exact (rationalWord_bounds q a).1.trans ha1

/-- This numerator is produced by the existing real stream multiplier. -/
def weightedOutputNumerator (q d : ℕ) (z : GaussianInt) (a : ℚ) : GaussianInt :=
  tdivN q (((2 : GaussianInt) ^ d * z) * rationalWord q a)

theorem weightedOutputNumerator_fits {q d w : ℕ} (hw : q + d + 4 ≤ w) (z : GaussianInt) (a : ℚ)
    (hz : ‖value q z‖ ≤ 4) (ha0 : 0 ≤ (a : ℝ)) (ha1 : (a : ℝ) ≤ 1) :
    Fits w (weightedOutputNumerator q d z a) := by
  have h := normalized_product_fits (q := q) (b := 0) (e := d + 2) (f := 0) (w := w)
    (by omega) ((2 : GaussianInt) ^ d * z) (rationalWord q a)
    (scaled_output_norm q d z hz) (by simpa using output_weight_norm q a ha0 ha1)
  simpa only [weightedOutputNumerator, Nat.add_zero] using h

/-- Both multiplier truncation and weight-table encoding are charged. The
latter is multiplied by the actual restored output magnitude. -/
theorem weightedOutputNumerator_error (q d : ℕ) (z : GaussianInt) (a : ℚ)
    (hz : ‖value q z‖ ≤ 4) :
    |(value q (weightedOutputNumerator q d z a)).re -
      (a : ℝ) * ((2 : ℝ) ^ d * (value q z).re)| ≤
      (2 + (2 : ℝ) ^ (d + 2)) / (2 : ℝ) ^ q := by
  let x := (2 : GaussianInt) ^ d * z
  have hprod := normalized_product_real_error q 0 x (rationalWord q a) rfl
  simp only [Nat.add_zero, pow_zero, one_mul] at hprod
  have hx : |(value q x).re| ≤ (2 : ℝ) ^ (d + 2) :=
    (Complex.abs_re_le_norm _).trans (scaled_output_norm q d z hz)
  have ha := rationalWord_error q a
  have hreal : (value q x).re = (2 : ℝ) ^ d * (value q z).re := by
    rw [show value q x = (2 : ℂ) ^ d * value q z from value_pow_two_mul q d z,
      show (2 : ℂ) ^ d = Complex.ofReal ((2 : ℝ) ^ d) by norm_cast,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← hreal]
  calc
    _ ≤ |(value q (weightedOutputNumerator q d z a)).re - (value q x).re * (value q (rationalWord q a)).re| +
        |(value q x).re * (value q (rationalWord q a)).re - (a : ℝ) * (value q x).re| := abs_sub_le _ _ _
    _ = |(value q (weightedOutputNumerator q d z a)).re - (value q x).re * (value q (rationalWord q a)).re| +
        |(value q x).re| * |(value q (rationalWord q a)).re - (a : ℝ)| := by
      congr 1
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ 2 / (2 : ℝ) ^ q + (2 : ℝ) ^ (d + 2) * (1 / (2 : ℝ) ^ q) :=
      add_le_add hprod (mul_le_mul hx ha (abs_nonneg _) (by positivity))
    _ = _ := by ring

/-- The restored magnitude costs `d+3` precision bits in the final weight stage. -/
theorem output_weight_precision {q d j : ℕ} (hq : d + j + 3 ≤ q) :
    (2 + (2 : ℝ) ^ (d + 2)) / (2 : ℝ) ^ q ≤ 1 / (2 : ℝ) ^ j := by
  have hd : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hnum : 2 + (2 : ℝ) ^ (d + 2) ≤ 2 ^ (d + 3) := by
    simp only [pow_add]
    norm_num
    linarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ ≤ (2 : ℝ) ^ (d + 3) * 2 ^ j := mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = (2 : ℝ) ^ (d + j + 3) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := by simpa only [one_mul] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq

/-- The cell scale is an exact numerator shift, including both ring factors. -/
theorem cell_output_scale (b l : ℕ) :
    (2 : ℝ) ^ (b + 2 * l + 2) = 4 * (2 : ℝ) ^ b * (2 ^ l : ℕ) ^ 2 := by
  simp only [Nat.cast_pow, Nat.cast_ofNat, two_mul, pow_add]
  ring

/-- The final similarity encoding needs two more bits than the triangular
stage budget, at the actual restored magnitude. -/
theorem cell_output_weight_precision {q b l j : ℕ} (hq : b + 2 * l + j + 5 ≤ q) :
    (2 + (2 : ℝ) ^ (b + 2 * l + 4)) / (2 : ℝ) ^ q ≤ 1 / (2 : ℝ) ^ j := by
  have h := output_weight_precision (q := q) (d := b + 2 * l + 2) (j := j) (by omega)
  simpa only [show b + 2 * l + 2 + 2 = b + 2 * l + 4 by omega] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
