import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp

/-! A certified integer approximation of `2^q exp (X / 2^q)` by the truncated
Taylor series, each term obtained from the previous one by one multiplication
and one truncated division: `T₀ = 2^q`, `T_{n+1} = (T_n X).tdiv (2^q (n+1))`.
Each term is within `∑_{i<n} |x|^i/i! ≤ e^{|x|}` of `2^q x^n/n!`, and the
Taylor tail after `N` terms is at most `|x|^N/N! e^{|x|}`. -/

namespace IntegerMultBounds.Resampling.ExpApprox

open Real Finset Nat

/-- The integer Taylor terms. -/
def expTerm (X : ℤ) (q : ℕ) : ℕ → ℤ
  | 0 => 2 ^ q
  | n + 1 => (expTerm X q n * X).tdiv (2 ^ q * (n + 1))

/-- The integer approximation of `2^q exp (X / 2^q)`. -/
def expApprox (X : ℤ) (q N : ℕ) : ℤ := ∑ n ∈ range N, expTerm X q n

theorem ediv_err (a b : ℤ) (hb : 0 < b) (ha : 0 ≤ a) : |((a / b : ℤ) : ℝ) - (a : ℝ) / b| ≤ 1 := by
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := Int.mul_ediv_add_emod a b
  have h2 := Int.emod_nonneg a hb.ne'
  have h3 := Int.emod_lt_of_pos a hb
  have e : (a : ℝ) = b * ((a / b : ℤ) : ℝ) + ((a % b : ℤ) : ℝ) := by exact_mod_cast h1.symm
  have h2' : (0 : ℝ) ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast h2
  have h3' : ((a % b : ℤ) : ℝ) < b := by exact_mod_cast h3
  rw [abs_le]; constructor
  · rw [neg_le_sub_iff_le_add, div_le_iff₀ hbr]; nlinarith
  · have : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
      rw [le_div_iff₀ hbr]; nlinarith
    linarith

/-- Truncated division is within one of the real quotient. -/
theorem tdiv_err (a b : ℤ) (hb : 0 < b) : |((a.tdiv b : ℤ) : ℝ) - (a : ℝ) / b| ≤ 1 := by
  rcases le_or_gt 0 a with ha | ha
  · rw [Int.tdiv_eq_ediv_of_nonneg ha]; exact ediv_err a b hb ha
  · have h := ediv_err (-a) b hb (by omega)
    rw [show a.tdiv b = -((-a).tdiv b) by rw [Int.neg_tdiv, neg_neg],
      Int.tdiv_eq_ediv_of_nonneg (by omega)]
    rw [← abs_neg]
    convert h using 2
    push_cast; ring

/-- Each integer term is within `∑_{i<n} |x|^i/i!` of `2^q x^n / n!`. -/
theorem expTerm_err (X : ℤ) (q : ℕ) (n : ℕ) :
    |(expTerm X q n : ℝ) - 2 ^ q * ((X : ℝ) / 2 ^ q) ^ n / (n ! : ℝ)| ≤
      ∑ i ∈ range n, |(X : ℝ) / 2 ^ q| ^ i / (i ! : ℝ) := by
  set x : ℝ := (X : ℝ) / 2 ^ q with hx
  have hq : (0 : ℝ) < 2 ^ q := by positivity
  induction n with
  | zero => simp [expTerm]
  | succ n ih =>
    have hb : (0 : ℤ) < 2 ^ q * (n + 1) := by positivity
    have h1 := tdiv_err (expTerm X q n * X) (2 ^ q * (n + 1)) hb
    have hquot : ((expTerm X q n * X : ℤ) : ℝ) / ((2 ^ q * (n + 1) : ℤ) : ℝ) =
        (expTerm X q n : ℝ) * x / (n + 1) := by
      rw [hx]; push_cast; field_simp
    rw [hquot] at h1
    have hfac : ((n + 1)! : ℝ) = (n + 1) * (n ! : ℝ) := by push_cast [Nat.factorial_succ]; ring
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hnf : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have e2 : (expTerm X q n : ℝ) * x / (n + 1) - 2 ^ q * x ^ (n + 1) / ((n + 1)! : ℝ) =
        x / (n + 1) * ((expTerm X q n : ℝ) - 2 ^ q * x ^ n / (n ! : ℝ)) := by
      rw [hfac]; field_simp; ring
    have h2 : |(expTerm X q n : ℝ) * x / (n + 1) - 2 ^ q * x ^ (n + 1) / ((n + 1)! : ℝ)| ≤
        |x| / (n + 1) * ∑ i ∈ range n, |x| ^ i / (i ! : ℝ) := by
      rw [e2, abs_mul, abs_div, abs_of_pos hn1]
      gcongr
    have hsum : |x| / (n + 1) * ∑ i ∈ range n, |x| ^ i / (i ! : ℝ) ≤
        ∑ i ∈ range n, |x| ^ (i + 1) / ((i + 1)! : ℝ) := by
      rw [mul_sum]
      refine sum_le_sum fun i hi => ?_
      simp only [mem_range] at hi
      have hfi : ((i + 1)! : ℝ) = (i + 1) * (i ! : ℝ) := by push_cast [Nat.factorial_succ]; ring
      have hif : (0 : ℝ) < (i ! : ℝ) := by exact_mod_cast Nat.factorial_pos i
      rw [hfi, pow_succ]
      have hle : ((i : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast (by omega : i + 1 ≤ n + 1)
      have hxa : 0 ≤ |x| := abs_nonneg x
      calc |x| / (n + 1) * (|x| ^ i / (i ! : ℝ)) = (|x| ^ i * |x|) / ((n + 1) * (i ! : ℝ)) := by
            field_simp
        _ ≤ (|x| ^ i * |x|) / ((i + 1) * (i ! : ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    show |((expTerm X q n * X).tdiv (2 ^ q * (n + 1)) : ℝ) - 2 ^ q * x ^ (n + 1) / ((n + 1)! : ℝ)| ≤ _
    rw [sum_range_succ', pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    calc _ ≤ |((expTerm X q n * X).tdiv (2 ^ q * (n + 1)) : ℝ) - (expTerm X q n : ℝ) * x / (n + 1)| +
          |(expTerm X q n : ℝ) * x / (n + 1) - 2 ^ q * x ^ (n + 1) / ((n + 1)! : ℝ)| := abs_sub_le _ _ _
      _ ≤ 1 + ∑ i ∈ range n, |x| ^ (i + 1) / ((i + 1)! : ℝ) := by
          push_cast at h1
          linarith
      _ = _ := by ring

theorem hasSum_exp (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n ! : ℝ)) (Real.exp x) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  rw [← Real.exp_eq_exp_ℝ] at h
  convert h using 1
  funext n; rw [smul_eq_mul, div_eq_inv_mul]

/-- The Taylor tail of `exp` after `N` terms is at most `|x|^N/N! e^{|x|}`. -/
theorem exp_tail (x : ℝ) (N : ℕ) :
    |Real.exp x - ∑ n ∈ range N, x ^ n / (n ! : ℝ)| ≤ |x| ^ N / (N ! : ℝ) * Real.exp |x| := by
  have hs := hasSum_exp x
  have ha := hasSum_exp |x|
  have hsplit := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at hsplit
  rw [← hsplit, add_sub_cancel_left]
  have hg : HasSum (fun k : ℕ => |x| ^ N / (N ! : ℝ) * (|x| ^ k / (k ! : ℝ)))
      (|x| ^ N / (N ! : ℝ) * Real.exp |x|) := ha.mul_left _
  have hb : ∀ k, ‖x ^ (k + N) / ((k + N) ! : ℝ)‖ ≤ |x| ^ N / (N ! : ℝ) * (|x| ^ k / (k ! : ℝ)) := by
    intro k
    rw [Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    have hf : ((N ! * k ! : ℕ) : ℝ) ≤ ((k + N) ! : ℝ) := by
      exact_mod_cast (by rw [add_comm]; exact Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add N k))
    have hN : (0 : ℝ) < (N ! : ℝ) := by exact_mod_cast Nat.factorial_pos N
    have hk : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    push_cast at hf
    rw [_root_.div_mul_div_comm, pow_add, mul_comm (|x| ^ k)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hf
  calc |∑' k, x ^ (k + N) / ((k + N) ! : ℝ)| = ‖∑' k, x ^ (k + N) / ((k + N) ! : ℝ)‖ := (Real.norm_eq_abs _).symm
    _ ≤ |x| ^ N / (N ! : ℝ) * Real.exp |x| := tsum_of_norm_bounded hg hb

/-- The integer Taylor sum is within `N e^{|x|} + 2^q |x|^N/N! e^{|x|}` of `2^q e^x`. -/
theorem expApprox_err (X : ℤ) (q N : ℕ) :
    |(expApprox X q N : ℝ) - 2 ^ q * Real.exp ((X : ℝ) / 2 ^ q)| ≤
      N * Real.exp |(X : ℝ) / 2 ^ q| +
        2 ^ q * (|(X : ℝ) / 2 ^ q| ^ N / (N ! : ℝ) * Real.exp |(X : ℝ) / 2 ^ q|) := by
  set x : ℝ := (X : ℝ) / 2 ^ q
  have hq : (0 : ℝ) < 2 ^ q := by positivity
  have hterms : |(expApprox X q N : ℝ) - 2 ^ q * ∑ n ∈ range N, x ^ n / (n ! : ℝ)| ≤ N * Real.exp |x| := by
    rw [expApprox, Int.cast_sum, mul_sum, ← sum_sub_distrib]
    calc _ ≤ ∑ n ∈ range N, |(expTerm X q n : ℝ) - 2 ^ q * (x ^ n / (n ! : ℝ))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ range N, Real.exp |x| := by
          refine sum_le_sum fun n _ => ?_
          rw [← mul_div_assoc]
          exact (expTerm_err X q n).trans (Real.sum_le_exp_of_nonneg (abs_nonneg x) n)
      _ = N * Real.exp |x| := by simp
  have htail := exp_tail x N
  have e : (expApprox X q N : ℝ) - 2 ^ q * Real.exp x =
      ((expApprox X q N : ℝ) - 2 ^ q * ∑ n ∈ range N, x ^ n / (n ! : ℝ)) -
        2 ^ q * (Real.exp x - ∑ n ∈ range N, x ^ n / (n ! : ℝ)) := by ring
  rw [e]
  calc _ ≤ |(expApprox X q N : ℝ) - 2 ^ q * ∑ n ∈ range N, x ^ n / (n ! : ℝ)| +
        |2 ^ q * (Real.exp x - ∑ n ∈ range N, x ^ n / (n ! : ℝ))| := abs_sub _ _
    _ ≤ _ := by
        rw [abs_mul, abs_of_pos hq]
        gcongr

end IntegerMultBounds.Resampling.ExpApprox
