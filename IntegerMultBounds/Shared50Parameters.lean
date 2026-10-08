import IntegerMultBounds.Parameters

/-! Exact arithmetic and the strict branching inequality for the optimized
50-point bit-network budget. The constants are recomputed from their formulas;
rank-balance and loss statements about an actual trace remain explicit premises
in the conditional arithmetic corollaries below. -/

namespace IntegerMultBounds.Shared50Parameters

/-- Ambient common-point count. -/
def h : ℕ := 50
/-- Triple-input dimension. -/
def v : ℕ := 19600
/-- Branch arity. -/
def m : ℕ := 125000
/-- Source tensor dimension. -/
def N : ℕ := v ^ 3
/-- Certified side-role budget per invocation. -/
def R : ℕ := 509194
/-- Full global wire budget. -/
def W : ℕ := 2 * N + 2 * v ^ 2 * (R + h)
/-- Proposed global rank-loss budget. -/
def L : ℕ := 3 * v ^ 2 * h ^ 2
/-- Positive source-dimension saving after twice the loss budget. -/
def D : ℕ := N - 2 * L
/-- Rank-sum budget obtained if the actual trace meets its balance and loss bounds. -/
def s : ℕ := W * m - D

/-- All optimized finite counts, independently recomputed in the kernel. -/
theorem counts :
    Nat.choose h 3 = v ∧ h ^ 3 = m ∧
    N = 7529536000000 ∧ R = 509194 ∧
    W = 406321422080000 ∧ L = 2881200000000 ∧
    D = 1767136000000 ∧ s = 50790175992864000000 := by
  decide +kernel

theorem dimension_count : Nat.choose 50 3 = 19600 := counts.1
theorem arity_count : (50 : ℕ) ^ 3 = 125000 := counts.2.1
theorem source_count : N = 7529536000000 := counts.2.2.1
theorem side_role_count : R = 509194 := rfl
theorem wire_count : W = 406321422080000 := counts.2.2.2.2.1
theorem loss_count : L = 2881200000000 := counts.2.2.2.2.2.1
theorem deficit_count : D = 1767136000000 := counts.2.2.2.2.2.2.1
theorem rank_count : s = 50790175992864000000 := counts.2.2.2.2.2.2.2

theorem wire_formula : W = 2 * N + 2 * v ^ 2 * (R + 50) := rfl
theorem deficit_balance : D + 2 * L = N := by
  rw [deficit_count, loss_count, source_count]

theorem rank_formula : s = W * m - N + 2 * L := by
  rw [rank_count, wire_count, source_count, loss_count]
  norm_num [m]

theorem rank_balance : s + N = W * m + 2 * L := by
  rw [rank_count, wire_count, source_count, loss_count]
  norm_num [m]

theorem positive_deficit : 0 < D ∧ 2 * L < N := by
  rw [deficit_count, loss_count, source_count]
  norm_num

theorem rank_range : 2 ≤ s ∧ s < m ^ 5 := by
  rw [rank_count]
  norm_num [m]

noncomputable section

/-- The exact normalized deficit and its strict slack over the selected saving. -/
theorem deficit_fraction :
    (D : ℝ) / (W * m) = 23 / 661055000 ∧
      1 - (s : ℝ) / (W * m) = 23 / 661055000 := by
  rw [deficit_count, wire_count, rank_count]
  norm_num [m]

theorem deficit_slack :
    (23 / 661055000 : ℝ) - (1 - Parameters.tau) * (11737 / 1000) =
      84861241 / 1652637500000000000 := by
  norm_num [Parameters.tau]

theorem deficit_strict :
    (1 - Parameters.tau) * (11737 / 1000 : ℝ) < 23 / 661055000 := by
  have hh := deficit_slack
  norm_num at hh ⊢
  linarith

/-- A finite exponential-series lower bound certifies the logarithm enclosure. -/
theorem log_bound : Real.log 125000 < 11737 / 1000 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have hseries := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 11737 / 1000 by norm_num) 25
  have hsum : (125000 : ℝ) <
      ∑ i ∈ Finset.range 25, (11737 / 1000 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hsum.trans_le hseries

/-- The optimized bit budget satisfies the existing chosen branching exponent. -/
theorem branching_bound : (s : ℝ) / W < (m : ℝ) ^ Parameters.tau := by
  have hlog := log_bound
  have hdef := deficit_strict
  have hpos : (0 : ℝ) < 1 - Parameters.tau := by norm_num [Parameters.tau]
  have hlin := mul_lt_mul_of_pos_left hlog hpos
  have hexp := Real.add_one_le_exp (-(1 - Parameters.tau) * Real.log 125000)
  have hr : (1 : ℝ) - 23 / 661055000 <
      Real.exp (-(1 - Parameters.tau) * Real.log 125000) := by linarith
  have heq : (125000 : ℝ) ^ Parameters.tau =
      125000 * Real.exp (-(1 - Parameters.tau) * Real.log 125000) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have he : Real.log 125000 * Parameters.tau =
        Real.log 125000 + -(1 - Parameters.tau) * Real.log 125000 := by ring
    rw [he, Real.exp_add, Real.exp_log (by norm_num)]
  rw [rank_count, wire_count]
  change (50790175992864000000 / 406321422080000 : ℝ) < (125000 : ℝ) ^ Parameters.tau
  rw [heq]
  nlinarith

/-- A rank-sum upper bound inherits the strict analytic branching inequality. -/
theorem branching_of_rank_le (rankSum : ℕ) (hr : rankSum ≤ s) :
    (rankSum : ℝ) / W < (m : ℝ) ^ Parameters.tau := by
  have hr' : (rankSum : ℝ) ≤ s := by exact_mod_cast hr
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hr' (by rw [wire_count]; positivity)) branching_bound

/-- This only discharges arithmetic after a genuine rank balance and loss
bound have been established for a concrete trace. -/
theorem rank_le_of_balance (rankSum loss : ℕ)
    (hb : rankSum + N ≤ W * m + 2 * loss) (hl : loss ≤ L) : rankSum ≤ s := by
  have he := rank_balance
  omega

theorem branching_of_balance (rankSum loss : ℕ)
    (hb : rankSum + N ≤ W * m + 2 * loss) (hl : loss ≤ L) :
    (rankSum : ℝ) / W < (m : ℝ) ^ Parameters.tau :=
  branching_of_rank_le rankSum (rank_le_of_balance rankSum loss hb hl)

end
end IntegerMultBounds.Shared50Parameters
