module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratorWords
public import IntegerMultBounds.NLogN.PhaseCellInteriorSolve
public import IntegerMultBounds.NLogN.PhaseCellWeightRange

/-! # Rational data for the three weight stages of a cell run

These constructors round the actual selected similarity sample, its reciprocal
and the products on computed inputs. No real rounding oracle is used. Their
tape implementations, intermediate word fits and costs remain open.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

/-- A normalization exponent covering the RHS and reciprocal-weight magnitudes. -/
def inputExponent (p cExp : ℕ) : ℕ := cExp + (8 * p + 1) + 1

/-- Rational real part of a stored Gaussian grid numerator. -/
def rationalValue (q : ℕ) (z : GaussianInt) : ℚ := (z.re : ℚ) / (2 : ℚ) ^ q

@[simp] theorem rationalValue_cast (q : ℕ) (z : GaussianInt) :
    (rationalValue q z : ℝ) = (value q z).re := by simp [rationalValue, value]

/-- The actual selected rational similarity weight at an ambient coordinate. -/
def weightData (s t p u : ℕ) (lo : ZMod s) (k : ℕ) : ℚ :=
  PhaseCellConcreteCoefficients.similarity (2 ^ 15 * p) s t u
    ((lo + (k : ZMod s)).val : ℤ)

@[simp] theorem weightData_cast (s t p u : ℕ) [NeZero s] (lo : ZMod s) (k : ℕ) :
    (weightData s t p u lo k : ℝ) = PhaseCellMatrix.weight s t p u lo k := rfl

/-- A computed reciprocal weight at the common arithmetic precision. -/
def reciprocalWeightWord (q : ℕ) (d : ℚ) : GaussianInt := rationalWord q (1 / d)

/-- Normalize the product of the raw input and the computed reciprocal weight. -/
def weightedInputWord (q b : ℕ) (c d : ℚ) : GaussianInt :=
  rationalWord q (c * rationalValue q (reciprocalWeightWord q d) / (2 : ℚ) ^ b)

/-- Final similarity multiplication is on the computed interior output. -/
def weightedOutputWord (q : ℕ) (d y : ℚ) : GaussianInt := rationalWord q (d * y)

theorem reciprocalWeightWord_error (q : ℕ) (d : ℚ) :
    |(value q (reciprocalWeightWord q d)).re - 1 / (d : ℝ)| ≤ 1 / (2 : ℝ) ^ q := by
  simpa only [reciprocalWeightWord, Rat.cast_div, Rat.cast_one] using rationalWord_error q (1 / d)

theorem weightedInputWord_error (q b : ℕ) (c d : ℚ) :
    |(2 : ℝ) ^ b * (value q (weightedInputWord q b c d)).re -
      (c : ℝ) * (value q (reciprocalWeightWord q d)).re| ≤ (2 : ℝ) ^ b / (2 : ℝ) ^ q := by
  have he := rationalWord_error q (c * rationalValue q (reciprocalWeightWord q d) / (2 : ℚ) ^ b)
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, rationalValue_cast] at he
  have hp : (0 : ℝ) < 2 ^ b := by positivity
  change |(value q (weightedInputWord q b c d)).re -
    (c : ℝ) * (value q (reciprocalWeightWord q d)).re / (2 : ℝ) ^ b| ≤ 1 / (2 : ℝ) ^ q at he
  calc
    _ = |(2 : ℝ) ^ b * ((value q (weightedInputWord q b c d)).re -
        (c : ℝ) * (value q (reciprocalWeightWord q d)).re / (2 : ℝ) ^ b)| := by
      congr 1
      field_simp
    _ = (2 : ℝ) ^ b * |(value q (weightedInputWord q b c d)).re -
        (c : ℝ) * (value q (reciprocalWeightWord q d)).re / (2 : ℝ) ^ b| := by
      rw [abs_mul, abs_of_pos hp]
    _ ≤ (2 : ℝ) ^ b * (1 / (2 : ℝ) ^ q) := mul_le_mul_of_nonneg_left he hp.le
    _ = _ := by ring

theorem weightedOutputWord_error (q : ℕ) (d y : ℚ) :
    |(value q (weightedOutputWord q d y)).re - (d : ℝ) * (y : ℝ)| ≤ 1 / (2 : ℝ) ^ q := by
  simpa only [weightedOutputWord, Rat.cast_mul] using rationalWord_error q (d * y)

/-- A positive lower bound on the actual weight bounds the encoded reciprocal;
downward rounding never amplifies this nonnegative value. -/
theorem reciprocalWeightWord_bounds {q e : ℕ} (d : ℚ)
    (hd : 1 / (2 : ℝ) ^ e ≤ (d : ℝ)) :
    0 ≤ (value q (reciprocalWeightWord q d)).re ∧
      (value q (reciprocalWeightWord q d)).re ≤ (2 : ℝ) ^ e := by
  have hd0 : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le (by positivity) hd
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd0
  constructor
  · exact rationalWord_nonneg q _ (by positivity)
  · apply (rationalWord_bounds q (1 / d)).1.trans
    simp only [Rat.cast_div, Rat.cast_one]
    apply (div_le_iff₀ hd0).mpr
    have h := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2 ^ e)
    simpa only [mul_one_div_cancel (by positivity : (2 : ℝ) ^ e ≠ 0)] using h

/-- A power-of-two normalization bounds the exact rational input to its grid
encoder, uniformly in cell length. -/
theorem weightedInput_argument_bound {q cExp e : ℕ} (c d : ℚ)
    (hc : |(c : ℝ)| ≤ (2 : ℝ) ^ cExp) (hd : 1 / (2 : ℝ) ^ e ≤ (d : ℝ)) :
    |((c * rationalValue q (reciprocalWeightWord q d) / (2 : ℚ) ^ (cExp + e + 1) : ℚ) : ℝ)| ≤ 1 / 2 := by
  obtain ⟨hr0, hr⟩ := reciprocalWeightWord_bounds (q := q) d hd
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, rationalValue_cast,
    abs_div, abs_mul, abs_of_nonneg hr0, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (cExp + e + 1))]
  apply (div_le_iff₀ (by positivity)).mpr
  calc
    _ ≤ (2 : ℝ) ^ cExp * (2 : ℝ) ^ e := mul_le_mul hc hr hr0 (by positivity)
    _ = 1 / 2 * (2 : ℝ) ^ (cExp + e + 1) := by rw [pow_add, pow_add]; ring

/-- The generated normalized inputs meet the same S1 disk contract as the
constructed inverse generators. -/
theorem weightedInputWord_disk {q cExp e : ℕ} (hq : 2 ≤ q) (c d : ℚ)
    (hc : |(c : ℝ)| ≤ (2 : ℝ) ^ cExp) (hd : 1 / (2 : ℝ) ^ e ≤ (d : ℝ)) :
    (weightedInputWord q (cExp + e + 1) c d).re ^ 2 +
      (weightedInputWord q (cExp + e + 1) c d).im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
  apply rationalWord_disk hq
  exact (weightedInput_argument_bound (q := q) c d hc hd).trans (by norm_num)

/-- The selected corrected samples supply the reciprocal-weight range without
an assumed weight table. Ambient phase coordinates are unchanged. -/
theorem weightData_bounds {s t p u : ℕ} {α d : ℝ} (hp : 0 < p) (hs : 0 < s)
    (hαu : α ^ 2 = (u : ℝ)) (hθ : 0 < (t : ℝ) / s - 1)
    (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (lo : ZMod s) (k : ℕ) :
    1 / (2 : ℝ) ^ (8 * p + 1) ≤ (weightData s t p u lo k : ℝ) ∧
      (weightData s t p u lo k : ℝ) ≤ 1 :=
  PhaseCellConcreteCoefficients.selected_similarity_range
    ((lo + (k : ZMod s)).val : ℤ) hp hs hαu hθ hgap hbudget

/-- Arithmetic precision pays for the normalized input product as well as the
two unscaled rounding stages. -/
theorem weight_stage_precision {b j q : ℕ} (hq : b + j ≤ q) :
    (2 : ℝ) ^ b / 2 ^ q ≤ 1 / (2 : ℝ) ^ j ∧ 1 / (2 : ℝ) ^ q ≤ 1 / (2 : ℝ) ^ j := by
  have hp : (2 : ℝ) ^ (b + j) ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
  have hscale : (2 : ℝ) ^ b / 2 ^ q ≤ 1 / (2 : ℝ) ^ j := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simpa only [← pow_add, one_mul] using hp
  refine ⟨hscale, ?_⟩
  have hb : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  exact (div_le_div_of_nonneg_right hb (by positivity)).trans hscale

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
