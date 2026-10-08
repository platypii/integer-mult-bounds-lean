import Mathlib.Tactic

/-! Uniform numerical bounds used in the local exceptional-record repair cost.
Counting the actual bad-address set and realizing sorting on tapes remain
separate obligations. The hypotheses here are explicit arithmetic inequalities.
-/

namespace IntegerMultBounds.Compact

theorem repair_density_bound (p n B C : ℝ) (hp : 0 < p) (hn : 0 ≤ n)
    (hnp : n ≤ p) (hB : 64 * p ^ 4 ≤ B) (hC : 1024 * p ^ 4 ≤ C) :
    2 * n / B + 8 * n / C ≤ 5 / (128 * p ^ 3) := by
  have hB₀ : 0 < 64 * p ^ 4 := by positivity
  have hC₀ : 0 < 1024 * p ^ 4 := by positivity
  calc
    2 * n / B + 8 * n / C ≤
        2 * n / (64 * p ^ 4) + 8 * n / (1024 * p ^ 4) := by
      exact add_le_add (div_le_div_of_nonneg_left (by positivity) hB₀ hB)
        (div_le_div_of_nonneg_left (by positivity) hC₀ hC)
    _ ≤ 2 * p / (64 * p ^ 4) + 8 * p / (1024 * p ^ 4) := by gcongr
    _ = 5 / (128 * p ^ 3) := by field_simp; ring

/-- The stated eventual cutoff implies the required radix lower bounds. -/
theorem dyadic_repair_radices (p : ℝ) (ell K : ℕ) (hp : 0 < p)
    (hell : p ≤ (2 : ℝ) ^ ell) (hK : 8 * ell + 16 ≤ K) :
    64 * p ^ 4 ≤ (2 : ℝ) ^ (4 * ell + 6) ∧
    1024 * p ^ 4 ≤ (2 : ℝ) ^ (K - (4 * ell + 6)) := by
  have hpow : p ^ 4 ≤ ((2 : ℝ) ^ ell) ^ 4 := by gcongr
  have hexp : (2 : ℝ) ^ (4 * ell) = ((2 : ℝ) ^ ell) ^ 4 := by
    rw [Nat.mul_comm, pow_mul]
  constructor
  · rw [pow_add, hexp]
    norm_num
    nlinarith
  · calc
      1024 * p ^ 4 ≤ (2 : ℝ) ^ (4 * ell + 10) := by
        rw [pow_add, hexp]
        norm_num
        nlinarith
      _ ≤ (2 : ℝ) ^ (K - (4 * ell + 6)) :=
        pow_le_pow_right₀ (by norm_num) (by omega)

theorem uniform_repair_density (p : ℝ) (n ell K : ℕ) (hp : 0 < p)
    (hn : (n : ℝ) ≤ p) (hell : p ≤ (2 : ℝ) ^ ell) (hK : 8 * ell + 16 ≤ K) :
    2 * n / (2 : ℝ) ^ (4 * ell + 6) +
      8 * n / (2 : ℝ) ^ (K - (4 * ell + 6)) ≤ 5 / (128 * p ^ 3) := by
  obtain ⟨hB, hC⟩ := dyadic_repair_radices p ell K hp hell hK
  exact repair_density_bound p n _ _ hp (by positivity) hn hB hC

/-- Once descriptor work is paid by records and the exceptional fraction is
small enough, the written repair cost expression is at most three volumes. -/
theorem repair_cost_linear (M R A δ : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hA : 0 ≤ A) (_hδ : 0 ≤ δ)
    (hAR : A ≤ R) (hsetup : A ^ 3 ≤ R) (hdensity : δ * A ≤ 1 / 2) :
    M * R + M * A ^ 3 + δ * M * A * (R + A) ≤ 3 * (M * R) := by
  have hwork : δ * A * (R + A) ≤ R := by
    calc
      δ * A * (R + A) ≤ (1 / 2 : ℝ) * (2 * R) := by gcongr; linarith
      _ = R := by ring
  have hs := mul_le_mul_of_nonneg_left hsetup hM
  have hw := mul_le_mul_of_nonneg_left hwork hM
  nlinarith

end IntegerMultBounds.Compact
