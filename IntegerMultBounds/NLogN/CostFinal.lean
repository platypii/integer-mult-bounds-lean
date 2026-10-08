import IntegerMultBounds.NLogN.JointRecurrence
import IntegerMultBounds.NLogN.ExpCostBound

/-! The final cost theorem of the subroutine, with concrete costs for the
small products and the weight evaluations.

`joint_cost_nlogn` closes the recurrence for any cost `M` bounded above the
threshold `2^(2^624)` by one full recursive step `stepOps₂` (three synthetic
convolution pipelines whose delegated `3rp`-bit products cost `M`, plus the
resampling maps with the paper's windows) and a linear overhead, provided the
weight evaluations and the `p`-bit products inside them have polylogarithmic
costs. Here those two costs are instantiated: the small products by the
envelope `Mcost₀ q = 10^6 q (log₂ q + 1)²` of the plain FFT multiplier's bit
count, and the weight evaluations by `expCost`, the binary-splitting evaluation
of the exponential with `Mcost₀` as multiplication cost.

Proved: `cost_final`. Its hypotheses are exactly: a family of grids `t n` of
positive lengths with product `transformSize n` and moduli `s n ≤ t n`; the
step structure `M n ≤ stepOps₂ … expCost Mcost₀ M + C n` for
`n ≥ 2^(2^624)`; and the a priori bound `M n ≤ 4·10^6 n (log₂ n)³` below the
threshold. Conclusion: `M n ≤ D n log n` for all `n ≥ 2`.

Not here: the grids and moduli are hypotheses. `ContractFinal` supplies them
(with exactness of the step) above its own threshold `2^(2^(1000·1729³))`,
which is larger than `2^(2^624)`; combining the two statements at that larger
threshold would require re-running the recurrence argument with that
threshold, which is not written. Tape steps are not modelled. -/

namespace IntegerMultBounds.NLogN

/-- `joint_cost_nlogn` with the weight-evaluation bound required only from
`q ≥ 16`, which is all the proof uses (it is applied at `q = precision n`,
which is at least `24576`). -/
theorem joint_cost_nlogn' (M Msmall Ecost : ℕ → ℕ) (K₀ K₁ C : ℕ)
    (s t : ℕ → Fin 1729 → ℕ)
    (ht : ∀ n i, 0 < t n i) (hst : ∀ n i, s n i ≤ t n i)
    (hT : ∀ n, ∏ j, t n j = transformSize n)
    (hE : ∀ q, 16 ≤ q → Ecost q ≤ K₀ * q * (Nat.log 2 q) ^ 4)
    (hM₀ : ∀ q, 2 ≤ q → Msmall q ≤ K₁ * q * (Nat.log 2 q) ^ 3)
    (hM : ∀ n, 2 ^ (2 ^ 624) ≤ n →
      M n ≤ stepOps₂ (rootSize 1729 n) (precision n) (modelExponents 1729 n) (s n) (t n)
        (paperWindowA (precision n) (alphaParam 1729 n))
        (paperWindowE (precision n) (alphaParam 1729 n)) (paperIter (alphaParam 1729 n))
        Ecost Msmall M + C * n)
    (hbase : ∀ n, 2 ≤ n → n < 2 ^ (2 ^ 624) → M n ≤ K₁ * n * (Nat.log 2 n) ^ 3) :
    ∃ D : ℝ, ∀ n, 2 ≤ n → (M n : ℝ) ≤ D * n * Real.log n := by
  have hd : 2 ≤ 1729 := by norm_num
  have hge : 2 ^ (1729 ^ 12) ≤ 2 ^ (2 ^ 624) := two_pow_le_two_pow paper_exp_le
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 30 * (K₀ + K₁ + 2) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ((2880 + 4320 * K * 1729 + C : ℕ) : ℝ) / Real.log 2 :=
    ⟨_, rfl⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : 0 ≤ A := by rw [hA]; exact div_nonneg (Nat.cast_nonneg _) hl2.le
  have hM0 : ∀ n, (0 : ℝ) ≤ (M n : ℝ) := fun n => Nat.cast_nonneg _
  have hparams : ∀ n, 2 ^ (2 ^ 624) ≤ n →
      (transformSize n : ℝ) * precision n ≤ 48 * n ∧
        2 ≤ 3 * rootSize 1729 n * precision n ∧ 3 * rootSize 1729 n * precision n < n ∧
        0 < rootSize 1729 n ∧
        Real.log (3 * (rootSize 1729 n : ℝ) * precision n) ≤
          (1 / (1729 : ℝ) + 1 / (2 * (1729 : ℝ) ^ 2)) * Real.log n :=
    fun n hn => recurrence_params (le_trans hge hn)
  have hbase' := base_of_polylog M K₁ (2 ^ 624) hbase
  have hrec : ∀ n, 2 ^ (2 ^ 624) ≤ n →
      (M n : ℝ) ≤ 12 * (transformSize n : ℝ) / rootSize 1729 n *
        (M (3 * rootSize 1729 n * precision n) : ℝ) + A * n * Real.log n := by
    intro n hn
    have hn' : 2 ^ (1729 ^ 12) ≤ n := le_trans hge hn
    have hb : 2 ^ 624 ≤ chunkSize n := chunkSize_ge_of_pow_le hn
    have hp16 : 16 ≤ precision n := le_trans (by norm_num) (precision_ge hd hn')
    have hp2 : 2 ≤ precision n := le_trans (by norm_num) hp16
    have hrow := row_threshold hd hn' hb Ecost Msmall K₀ K₁ (hE _ hp16) (hM₀ _ hp2)
    rw [← hK] at hrow
    have h := le_trans (hM n hn)
      (Nat.add_le_add_right (stepOps₂_params_le hn' (s n) (t n) (ht n) (hst n) (hT n)
        Ecost Msmall M K hrow) _)
    have h2 := step_cost_rec_real hn' M (2880 + 4320 * K * 1729) C h
    rw [hA]
    push_cast at h2 ⊢
    exact h2
  exact main_bound (T := transformSize) (r := rootSize 1729) (p := precision)
    (n₀ := 2 ^ (2 ^ 624)) (M := fun n => (M n : ℝ)) hA0 (two_le_two_pow_two_pow 624) hM0
    hparams hrec hbase'

/-- The final cost theorem. A cost `M` that, above the threshold, is at most one
full recursive step with the weight evaluations costed by `expCost` and the
small products by `Mcost₀` (the delegated `3rp`-bit products costed by `M`
itself) plus a linear overhead, and below the threshold is at most the plain
multiplier's `4·10^6 n (log₂ n)³`, is `O(n log n)`. -/
theorem cost_final (M : ℕ → ℕ) (C : ℕ) (s t : ℕ → Fin 1729 → ℕ)
    (ht : ∀ n i, 0 < t n i) (hst : ∀ n i, s n i ≤ t n i)
    (hT : ∀ n, ∏ j, t n j = transformSize n)
    (hM : ∀ n, 2 ^ (2 ^ 624) ≤ n →
      M n ≤ stepOps₂ (rootSize 1729 n) (precision n) (modelExponents 1729 n) (s n) (t n)
        (paperWindowA (precision n) (alphaParam 1729 n))
        (paperWindowE (precision n) (alphaParam 1729 n)) (paperIter (alphaParam 1729 n))
        expCost Mcost₀ M + C * n)
    (hbase : ∀ n, 2 ≤ n → n < 2 ^ (2 ^ 624) → M n ≤ 4 * 10 ^ 6 * n * (Nat.log 2 n) ^ 3) :
    ∃ D : ℝ, ∀ n, 2 ≤ n → (M n : ℝ) ≤ D * n * Real.log n :=
  joint_cost_nlogn' M Mcost₀ expCost (16 * 10 ^ 11) (4 * 10 ^ 6) C s t ht hst hT
    (fun _ hq => expCost_le_log4 hq) (fun _ hq => Mcost₀_le_cube hq) hM hbase

end IntegerMultBounds.NLogN
