module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvExec
public import IntegerMultBounds.MathlibTM2.Fast.CMulArith

/-! # Exact grid interpretation of weighted chirp operands

The real stream multiplier truncates at precision `q`. Interpreting its result at
precision `q+1` supplies exactly the factor one half in the chirp ring records.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

theorem value_eq_grid (p : ℕ) (z : GaussianInt) :
    value p z = GaussianInt.toComplex z / (2 : ℂ) ^ p := by
  rw [two_pow_complex]
  apply Complex.ext
  · exact (toComplex_div_re z ((2 : ℝ) ^ p)).symm
  · exact (toComplex_div_im z ((2 : ℝ) ^ p)).symm

theorem value_succ (p : ℕ) (z : GaussianInt) :
    value (p + 1) z = value p z / 2 := by
  rw [value_eq_grid, value_eq_grid, pow_succ, div_div]

theorem value_real (p : ℕ) (g : ℤ) :
    value p (⟨g, 0⟩ : GaussianInt) = (((g : ℝ) / 2 ^ p : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [value, Complex.ofReal_im, Int.cast_zero, zero_div]

/-- Unit-disk decoded values give the integer disk condition required by packing. -/
theorem disk_of_norm_value_le (p : ℕ) (z : GaussianInt) (h : ‖value p z‖ ≤ 1) :
    z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p) := by
  have hsq := mul_self_le_mul_self (norm_nonneg (value p z)) h
  rw [← pow_two, Complex.sq_norm, Complex.normSq_apply] at hsq
  simp only [value, ← pow_two] at hsq
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hscale : (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * p) := by
    rw [Nat.mul_comm 2 p, pow_mul]
    apply (div_le_one (by positivity : (0 : ℝ) < (2 ^ p) ^ 2)).1
    simpa only [add_div, div_pow, one_pow, Nat.mul_comm 2 p] using hsq
  exact_mod_cast hscale

/-- Exact semantics of the truncated product computed by the stream multiplier. -/
theorem value_tdivN_mul (p : ℕ) (x y : GaussianInt) :
    value p (tdivN p (x * y)) = rhoC p (value p x * value p y) := by
  simp only [value_eq_grid]
  exact (rhoC_mul_grid p x y).symm

/-- A real weight needs no extra machine shift to produce the half-scaled ring input. -/
theorem value_weighted (q : ℕ) (x : GaussianInt) (g : ℤ) :
    value (q + 1) (tdivN q (x * (⟨g, 0⟩ : GaussianInt))) =
      rhoC q ((((g : ℝ) / 2 ^ q : ℝ) : ℂ) * value q x) / 2 := by
  rw [value_succ, value_tdivN_mul, value_real, mul_comm]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
