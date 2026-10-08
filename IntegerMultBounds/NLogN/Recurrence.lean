import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! The contraction recurrence behind Harvey–van der Hoeven's `O(n log n)`
bound. With `T n := M n / (n log n)` the normalised cost, the paper obtains
`T n ≤ (K / d) · T n' + C` for a smaller size `n' < n` and `K / d < 1`, so `T`
is bounded. Here that step is proved abstractly: any contraction with a
strictly descending size map and a bounded base range is uniformly bounded, and
this is specialised to the `n log n` form. Nothing here constructs a
multiplication algorithm or establishes any recurrence for an actual cost. -/

namespace IntegerMultBounds.NLogN

/-- A contraction with a strictly descending size map is bounded everywhere by
`B + C / (1 - ρ)`, where `B` bounds the base range. -/
theorem bounded_of_contraction {T : ℕ → ℝ} {f : ℕ → ℕ} {ρ C B : ℝ} {n₀ : ℕ}
    (hρ₀ : 0 ≤ ρ) (hρ : ρ < 1) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hf : ∀ n, n₀ ≤ n → f n < n)
    (hT : ∀ n, n₀ ≤ n → T n ≤ ρ * T (f n) + C)
    (hbase : ∀ n, n < n₀ → T n ≤ B) :
    ∀ n, T n ≤ B + C / (1 - ρ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h1ρ : 0 < 1 - ρ := by linarith
    have hD : C / (1 - ρ) * (1 - ρ) = C := div_mul_cancel₀ C h1ρ.ne'
    have hD0 : 0 ≤ C / (1 - ρ) := div_nonneg hC h1ρ.le
    by_cases hn : n < n₀
    · linarith [hbase n hn]
    · rw [not_lt] at hn
      have hkey : ρ * (B + C / (1 - ρ)) + C ≤ B + C / (1 - ρ) := by
        nlinarith [mul_nonneg h1ρ.le hB]
      calc T n ≤ ρ * T (f n) + C := hT n hn
        _ ≤ ρ * (B + C / (1 - ρ)) + C := by gcongr; exact ih (f n) (hf n hn)
        _ ≤ B + C / (1 - ρ) := hkey

/-- The `n log n` form: a cost `M` whose normalised value contracts onto a
strictly smaller size `f n ≥ 2` is `O(n log n)` on every `n ≥ 2`. -/
theorem mul_cost_of_contraction {M : ℕ → ℝ} {f : ℕ → ℕ} {ρ C B : ℝ} {n₀ : ℕ}
    (hρ₀ : 0 ≤ ρ) (hρ : ρ < 1) (hC : 0 ≤ C) (hB : 0 ≤ B) (hn₀ : 2 ≤ n₀)
    (hf : ∀ n, n₀ ≤ n → 2 ≤ f n ∧ f n < n)
    (hM : ∀ n, n₀ ≤ n → M n ≤
      ρ * ((n : ℝ) * Real.log n / ((f n : ℝ) * Real.log (f n))) * M (f n) +
        C * n * Real.log n)
    (hbase : ∀ n, 2 ≤ n → n < n₀ → M n ≤ B * n * Real.log n) :
    ∃ D, ∀ n, 2 ≤ n → M n ≤ D * n * Real.log n := by
  have hpos : ∀ n : ℕ, 2 ≤ n → 0 < (n : ℝ) * Real.log n := fun n hn => by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    exact mul_pos (by linarith) (Real.log_pos this)
  let T : ℕ → ℝ := fun n => if 2 ≤ n then M n / (n * Real.log n) else 0
  have hT : ∀ n, n₀ ≤ n → T n ≤ ρ * T (f n) + C := by
    intro n hn
    have h2 : 2 ≤ n := le_trans hn₀ hn
    obtain ⟨hf2, _⟩ := hf n hn
    show (if 2 ≤ n then M n / (n * Real.log n) else 0) ≤
      ρ * (if 2 ≤ f n then M (f n) / (f n * Real.log (f n)) else 0) + C
    rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true hf2), div_le_iff₀ (hpos n h2)]
    have hp := hpos (f n) hf2
    calc M n ≤ _ := hM n hn
      _ = (ρ * (M (f n) / ((f n : ℝ) * Real.log (f n))) + C) *
          ((n : ℝ) * Real.log n) := by
        field_simp
  have hbase' : ∀ n, n < n₀ → T n ≤ B := by
    intro n hn
    show (if 2 ≤ n then M n / (n * Real.log n) else 0) ≤ B
    split_ifs with h2
    · rw [div_le_iff₀ (hpos n h2), ← mul_assoc]
      exact hbase n h2 hn
    · exact hB
  have hb := bounded_of_contraction hρ₀ hρ hC hB (fun n hn => (hf n hn).2) hT hbase'
  refine ⟨B + C / (1 - ρ), fun n hn => ?_⟩
  have := hb n
  change (if 2 ≤ n then M n / (n * Real.log n) else 0) ≤ _ at this
  rw [ite_eq_left_of_eq_true _ _ (eq_true hn), div_le_iff₀ (hpos n hn)] at this
  rw [mul_assoc]
  exact this

/-- Finite iteration of the contraction: the geometric overhead sum of any
depth is at most `C / (1 - ρ)`. -/
theorem geom_tail_le {ρ C : ℝ} (hρ₀ : 0 ≤ ρ) (hρ : ρ < 1) (hC : 0 ≤ C) (k : ℕ) :
    ∑ i ∈ Finset.range k, ρ ^ i * C ≤ C / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith
  rw [← Finset.sum_mul, le_div_iff₀ h1, mul_right_comm, geom_sum_mul_neg]
  nlinarith [mul_nonneg hC (pow_nonneg hρ₀ k)]

end IntegerMultBounds.NLogN
