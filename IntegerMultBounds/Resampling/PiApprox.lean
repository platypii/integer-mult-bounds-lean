import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! A certified integer approximation of `2^q π` by Machin's formula,
computed with natural-number divisions only: the `k`-th term of
`2^q arctan (1/m)` is `⌊2^q / ((2k+1) m^(2k+1))⌋`, the series is cut after `K`
terms, and `π = 16 arctan (1/5) - 4 arctan (1/239)`. -/

namespace IntegerMultBounds.Resampling.PiApprox

open Real Finset

/-- The truncated integer arctan sum. -/
def atanSum (m q : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => atanSum m q k + (-1) ^ k * ((2 ^ q / m ^ (2 * k + 1) / (2 * k + 1) : ℕ) : ℤ)

/-- The integer approximation of `2^q π`. -/
def piApprox (q K : ℕ) : ℤ := 4 * (4 * atanSum 5 q K - atanSum 239 q K)

theorem atanSum_eq (m q K : ℕ) :
    atanSum m q K = ∑ k ∈ range K, (-1) ^ k * ((2 ^ q / m ^ (2 * k + 1) / (2 * k + 1) : ℕ) : ℤ) := by
  induction K with
  | zero => rfl
  | succ K ih => rw [atanSum, ih, sum_range_succ]

/-- Each floored term is within one of its real value. -/
theorem term_err (m q k : ℕ) (hm : 0 < m) :
    |(((2 ^ q / m ^ (2 * k + 1) / (2 * k + 1) : ℕ) : ℝ)) - (2 : ℝ) ^ q * ((1 / m : ℝ) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))| ≤ 1 := by
  rw [Nat.div_div_eq_div_mul]
  set D := m ^ (2 * k + 1) * (2 * k + 1) with hD
  have hDpos : 0 < D := by positivity
  have hval : (2 : ℝ) ^ q * ((1 / m : ℝ) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) = ((2 ^ q : ℕ) : ℝ) / (D : ℝ) := by
    rw [hD]; push_cast; rw [one_div, inv_pow]; field_simp
  rw [hval]
  have h1 := Nat.div_add_mod (2 ^ q) D
  have h2 := Nat.mod_lt (2 ^ q) hDpos
  have hDr : (0 : ℝ) < D := by exact_mod_cast hDpos
  rw [abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add]
    rw [div_le_iff₀ hDr]
    have : ((2 ^ q : ℕ) : ℝ) = (D : ℝ) * ((2 ^ q / D : ℕ) : ℝ) + ((2 ^ q % D : ℕ) : ℝ) := by
      exact_mod_cast h1.symm
    have h3 : ((2 ^ q % D : ℕ) : ℝ) < D := by exact_mod_cast h2
    nlinarith
  · have := Nat.cast_div_le (α := ℝ) (m := 2 ^ q) (n := D)
    linarith

/-- The arctan series cut after `K` terms, for `0 ≤ x ≤ 1/2`, errs by at most `2 x^(2K+1)`. -/
theorem arctan_tail (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (K : ℕ) :
    |arctan x - ∑ k ∈ range K, (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1 : ℕ)| ≤ 2 * x ^ (2 * K + 1) := by
  set f : ℕ → ℝ := fun k => (-1) ^ k * x ^ (2 * k + 1) / ↑(2 * k + 1) with hf
  have hs : HasSum f (arctan x) := Real.hasSum_arctan (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; linarith)
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hg : Summable fun k : ℕ => x ^ (2 * (k + K) + 1) := by
    have : (fun k : ℕ => x ^ (2 * (k + K) + 1)) = fun k => x ^ (2 * K + 1) * (x ^ 2) ^ k := by
      funext k; rw [← pow_mul, ← pow_add]; ring_nf
    rw [this]
    exact (summable_geometric_of_lt_one (by positivity) hx2).mul_left _
  have hfa : ∀ k, ‖f (k + K)‖ ≤ x ^ (2 * (k + K) + 1) := by
    intro k
    simp only [hf, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
      abs_of_nonneg hx0]
    rw [Nat.abs_cast]
    exact div_le_self (by positivity) (by exact_mod_cast (by omega : 1 ≤ 2 * (k + K) + 1))
  have hsplit := (hs.summable.sum_add_tsum_nat_add K)
  rw [hs.tsum_eq] at hsplit
  rw [← hsplit, add_sub_cancel_left]
  have hsf : Summable fun k => f (k + K) := (summable_nat_add_iff K).mpr hs.summable
  calc |∑' k, f (k + K)| = ‖∑' k, f (k + K)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k, x ^ (2 * (k + K) + 1) := tsum_of_norm_bounded hg.hasSum hfa
    _ = x ^ (2 * K + 1) * (1 - x ^ 2)⁻¹ := by
        have : (fun k : ℕ => x ^ (2 * (k + K) + 1)) = fun k => x ^ (2 * K + 1) * (x ^ 2) ^ k := by
          funext k; rw [← pow_mul, ← pow_add]; ring_nf
        rw [this, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hx2]
    _ ≤ x ^ (2 * K + 1) * 2 := by
        gcongr
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        nlinarith
    _ = 2 * x ^ (2 * K + 1) := by ring

theorem atanSum_err (m q K : ℕ) (hm : 2 ≤ m) :
    |(atanSum m q K : ℝ) - 2 ^ q * arctan (1 / m)| ≤ K + 2 * 2 ^ q * (1 / m : ℝ) ^ (2 * K + 1) := by
  have hx0 : (0 : ℝ) ≤ 1 / m := by positivity
  have hx : (1 / m : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; norm_num; exact_mod_cast hm
  have ht := arctan_tail (1 / m) hx0 hx K
  set c : ℕ → ℝ := fun k => (2 : ℝ) ^ q * ((1 / m : ℝ) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))
  have hsum : (atanSum m q K : ℝ) - 2 ^ q * (∑ k ∈ range K, (-1) ^ k * (1 / m : ℝ) ^ (2 * k + 1) / (2 * k + 1 : ℕ)) =
      ∑ k ∈ range K, (-1) ^ k * ((((2 ^ q / m ^ (2 * k + 1) / (2 * k + 1) : ℕ) : ℝ)) - c k) := by
    rw [atanSum_eq, mul_sum, Int.cast_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    simp only [c, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    ring
  have hle : |∑ k ∈ range K, (-1) ^ k * ((((2 ^ q / m ^ (2 * k + 1) / (2 * k + 1) : ℕ) : ℝ)) - c k)| ≤ K := by
    calc _ ≤ ∑ k ∈ range K, |(-1) ^ k * ((((2 ^ q / m ^ (2 * k + 1) / (2 * k + 1) : ℕ) : ℝ)) - c k)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ range K, (1 : ℝ) := by
          refine sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
          exact term_err m q k (by omega)
      _ = K := by simp
  have hsplit : (atanSum m q K : ℝ) - 2 ^ q * arctan (1 / m) =
      ((atanSum m q K : ℝ) - 2 ^ q * (∑ k ∈ range K, (-1) ^ k * (1 / m : ℝ) ^ (2 * k + 1) / (2 * k + 1 : ℕ))) -
        2 ^ q * (arctan (1 / m) - ∑ k ∈ range K, (-1) ^ k * (1 / m : ℝ) ^ (2 * k + 1) / (2 * k + 1 : ℕ)) := by ring
  rw [hsplit, hsum]
  have hp : (0 : ℝ) < 2 ^ q := by positivity
  calc _ ≤ |∑ k ∈ range K, (-1) ^ k * ((((2 ^ q / m ^ (2 * k + 1) / (2 * k + 1) : ℕ) : ℝ)) - c k)| +
        |2 ^ q * (arctan (1 / m) - ∑ k ∈ range K, (-1) ^ k * (1 / m : ℝ) ^ (2 * k + 1) / (2 * k + 1 : ℕ))| :=
        abs_sub _ _
    _ ≤ K + 2 ^ q * (2 * (1 / m : ℝ) ^ (2 * K + 1)) := by
        rw [abs_mul, abs_of_pos hp]
        gcongr
    _ = K + 2 * 2 ^ q * (1 / m : ℝ) ^ (2 * K + 1) := by ring

/-- Machin's formula in integers: `piApprox q K` is within `20 K + 20 · 2^q / 5^(2K+1)` of `2^q π`. -/
theorem piApprox_err (q K : ℕ) :
    |(piApprox q K : ℝ) - 2 ^ q * π| ≤ 20 * K + 40 * 2 ^ q * (1 / 5 : ℝ) ^ (2 * K + 1) := by
  have h5 := atanSum_err 5 q K (by norm_num)
  have h239 := atanSum_err 239 q K (by norm_num)
  have hmachin := four_mul_arctan_inv_5_sub_arctan_inv_239
  have e : (piApprox q K : ℝ) - 2 ^ q * π =
      16 * ((atanSum 5 q K : ℝ) - 2 ^ q * arctan (1 / 5)) - 4 * ((atanSum 239 q K : ℝ) - 2 ^ q * arctan (1 / 239)) := by
    have : π = 4 * (4 * arctan (1 / 5) - arctan (1 / 239)) := by
      rw [one_div, one_div]; linarith
    rw [this, piApprox]; push_cast; ring
  have hm : (1 / 239 : ℝ) ^ (2 * K + 1) ≤ (1 / 5 : ℝ) ^ (2 * K + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hp : (0 : ℝ) ≤ 2 ^ q := by positivity
  rw [e]
  push_cast at h5 h239
  calc _ ≤ |16 * ((atanSum 5 q K : ℝ) - 2 ^ q * arctan (1 / 5))| + |4 * ((atanSum 239 q K : ℝ) - 2 ^ q * arctan (1 / 239))| :=
        abs_sub _ _
    _ = 16 * |(atanSum 5 q K : ℝ) - 2 ^ q * arctan (1 / 5)| + 4 * |(atanSum 239 q K : ℝ) - 2 ^ q * arctan (1 / 239)| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ 16 * (K + 2 * 2 ^ q * (1 / 5 : ℝ) ^ (2 * K + 1)) + 4 * (K + 2 * 2 ^ q * (1 / 239 : ℝ) ^ (2 * K + 1)) := by
        gcongr
    _ ≤ 20 * K + 40 * 2 ^ q * (1 / 5 : ℝ) ^ (2 * K + 1) := by nlinarith

end IntegerMultBounds.Resampling.PiApprox
