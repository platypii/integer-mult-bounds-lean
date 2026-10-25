module

public import IntegerMultBounds.NLogN.PhaseCellGeneratorData
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvDecode
import Mathlib.Data.Rat.Floor

/-! # Dyadic words for computable rational phase-cell setup data

Rational floor arithmetic produces ordinary real Gaussian numerators. Accuracy
and range are proved independently of a tape implementation of this encoding.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Downward rounding of a rational value to a real Gaussian grid word. -/
def rationalWord (q : ℕ) (x : ℚ) : GaussianInt := ⟨⌊(2 : ℚ) ^ q * x⌋, 0⟩

@[simp] theorem rationalWord_im (q : ℕ) (x : ℚ) : (rationalWord q x).im = 0 := rfl

/-- The real interpretation uses the same floor as the computable rational one. -/
theorem rationalWord_value_re (q : ℕ) (x : ℚ) :
    (value q (rationalWord q x)).re = (⌊(2 : ℝ) ^ q * (x : ℝ)⌋ : ℝ) / 2 ^ q := by
  simp only [value, rationalWord]
  rw [← Rat.floor_cast (α := ℝ)]
  norm_cast

theorem rationalWord_bounds (q : ℕ) (x : ℚ) :
    (value q (rationalWord q x)).re ≤ (x : ℝ) ∧
      (x : ℝ) - (value q (rationalWord q x)).re < 1 / (2 : ℝ) ^ q := by
  rw [rationalWord_value_re]
  have hp : (0 : ℝ) < 2 ^ q := by positivity
  have hlo := Int.floor_le ((2 : ℝ) ^ q * (x : ℝ))
  have hhi := Int.lt_floor_add_one ((2 : ℝ) ^ q * (x : ℝ))
  constructor
  · apply (div_le_iff₀ hp).mpr
    nlinarith
  · apply (mul_lt_mul_iff_right₀ hp).mp
    field_simp
    nlinarith

theorem rationalWord_error (q : ℕ) (x : ℚ) :
    |(value q (rationalWord q x)).re - (x : ℝ)| ≤ 1 / (2 : ℝ) ^ q := by
  obtain ⟨hlo, hhi⟩ := rationalWord_bounds q x
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  linarith

/-- Nonnegative scalar data remain nonnegative and do not grow on encoding. -/
theorem rationalWord_nonneg (q : ℕ) (x : ℚ) (hx : 0 ≤ x) :
    0 ≤ (value q (rationalWord q x)).re := by
  rw [rationalWord_value_re]
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg (by positivity) (by exact_mod_cast hx))

/-- Slack in a normalized generator absorbs its encoding error. -/
theorem rationalWord_abs_le_one {q : ℕ} (hq : 2 ≤ q) (x : ℚ) (hx : |(x : ℝ)| ≤ 3 / 4) :
    |(value q (rationalWord q x)).re| ≤ 1 := by
  have hp : (4 : ℝ) ≤ 2 ^ q := by
    convert (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq) using 1 <;> norm_num
  have he := rationalWord_error q x
  have he' : 1 / (2 : ℝ) ^ q ≤ 1 / 4 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    simpa using hp
  have ht := abs_add_le ((value q (rationalWord q x)).re - (x : ℝ)) (x : ℝ)
  rw [sub_add_cancel] at ht
  linarith

/-- The normalized real Gaussian word lies in the S1 numerator disk. -/
theorem rationalWord_disk {q : ℕ} (hq : 2 ≤ q) (x : ℚ) (hx : |(x : ℝ)| ≤ 3 / 4) :
    (rationalWord q x).re ^ 2 + (rationalWord q x).im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
  have hv := rationalWord_abs_le_one hq x hx
  have hn : |((rationalWord q x).re : ℝ)| ≤ (2 : ℝ) ^ q := by
    have hp : (0 : ℝ) < 2 ^ q := by positivity
    have hv' : |((rationalWord q x).re : ℝ)| / 2 ^ q ≤ 1 := by
      simpa only [value, abs_div, abs_of_pos hp] using hv
    simpa only [one_mul] using (div_le_iff₀ hp).mp hv'
  have hz : |(rationalWord q x).re| ≤ (2 : ℤ) ^ q := by exact_mod_cast hn
  have hs := (sq_le_sq₀ (abs_nonneg (rationalWord q x).re)
    (show (0 : ℤ) ≤ 2 ^ q by positivity)).mpr hz
  simpa only [sq_abs, ← pow_mul, mul_comm q 2, rationalWord_im, zero_pow (by omega : 2 ≠ 0), add_zero] using hs

@[simp] theorem rationalWord_zero (q : ℕ) : rationalWord q 0 = 0 := by
  ext <;> simp [rationalWord]

/-- Real words have no hidden imaginary contribution to their norm. -/
theorem rationalWord_norm (q : ℕ) (x : ℚ) :
    ‖value q (rationalWord q x)‖ = |(value q (rationalWord q x)).re| := by
  have hv : value q (rationalWord q x) = ((value q (rationalWord q x)).re : ℂ) := by
    apply Complex.ext <;> simp only [value, rationalWord, Complex.ofReal_re, Complex.ofReal_im, Int.cast_zero, zero_div]
  conv_lhs => rw [hv, Complex.norm_real, Real.norm_eq_abs]

/-- Encode a generator at scale two, leaving range slack for grid rounding. -/
def normalizedWords (q : ℕ) (xs : List ℚ) : List GaussianInt :=
  xs.map (fun x => rationalWord q (x / 2))

@[simp] theorem normalizedWords_length (q : ℕ) (xs : List ℚ) :
    (normalizedWords q xs).length = xs.length := by simp [normalizedWords]

theorem normalizedWords_block (q : ℕ) (xs : List ℚ) (i : ℕ) :
    block (normalizedWords q xs) i = rationalWord q (xs.getD i 0 / 2) := by
  change (xs.map (fun x => rationalWord q (x / 2))).getD i 0 = _
  have hz : rationalWord q ((0 : ℚ) / 2) = 0 := by simp
  rw [← hz]
  exact List.getD_map (l := xs) (d := (0 : ℚ)) (fun x => rationalWord q (x / 2))

theorem normalizedWords_error (q : ℕ) (xs : List ℚ) (i : ℕ) :
    |2 * (value q (block (normalizedWords q xs) i)).re - (xs.getD i 0 : ℝ)| ≤
      2 / (2 : ℝ) ^ q := by
  rw [normalizedWords_block]
  have h := rationalWord_error q (xs.getD i 0 / 2)
  push_cast at h
  calc
    _ = 2 * |(value q (rationalWord q (xs.getD i 0 / 2))).re - (xs.getD i 0 : ℝ) / 2| := by
      rw [← abs_of_pos (by norm_num : (0 : ℝ) < 2), ← abs_mul]
      congr 1
      ring
    _ ≤ 2 * (1 / (2 : ℝ) ^ q) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

theorem normalizedWords_disk {q : ℕ} (hq : 2 ≤ q) (xs : List ℚ)
    (hxs : ∀ x ∈ xs, |(x : ℝ)| ≤ 3 / 2) :
    ∀ z ∈ normalizedWords q xs, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  apply rationalWord_disk hq
  rw [Rat.cast_div, Rat.cast_ofNat, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := hxs x hx
  linarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
