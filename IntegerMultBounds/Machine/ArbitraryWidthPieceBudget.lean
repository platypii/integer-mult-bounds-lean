import IntegerMultBounds.Machine.ArbitraryWidthPieces
import IntegerMultBounds.Machine.Shared50RecursiveRootExecution

/-! The actual proved root budgets summed over the literal arbitrary-width
partition. This bounds the power-piece calls; physical view construction and
padding must still be charged by the general-width wrapper. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPieceBudget
noncomputable section
open Networks
open ArbitraryWidthPieces (depths)
open Shared50RecursiveRootExecution (rootBudget)

def constant : ℝ :=
  Shared50RecursiveRootExecution.constant *
    (((125000 : ℝ)-1)*(125000 : ℝ)^Parameters.tau / ((125000 : ℝ)^Parameters.tau-1))

theorem constant_positive : 0 < constant := by
  have hx : 1 < (125000 : ℝ)^Parameters.tau :=
    Real.one_lt_rpow (by norm_num) Shared50RecursiveBudgetBound.exponent_range.1
  unfold constant
  exact mul_pos Shared50RecursiveRootExecution.constant_positive
    (div_pos (mul_pos (by norm_num) (by linarith)) (by linarith))

/-- The cost of every actual power-width call in the literal partition sums
to the same certified width exponent. No wrapper execution premise is used. -/
theorem sum_bound (V e k : ℕ) (hk : 125000^k ≤ e) :
    ((depths 125000 e k).map (fun j => (rootBudget j V : ℝ))).sum ≤
      constant*(V : ℝ)*(e : ℝ)^Parameters.tau := by
  let C := Shared50RecursiveRootExecution.constant
  have hCV : 0 ≤ C*(V : ℝ) :=
    mul_nonneg Shared50RecursiveRootExecution.constant_positive.le (Nat.cast_nonneg _)
  calc
    ((depths 125000 e k).map (fun j => (rootBudget j V : ℝ))).sum =
        ∑ j ∈ Finset.range (k+1), (e/125000^j%125000 : ℕ)*(rootBudget j V : ℝ) :=
      ArbitraryWidthPieces.real_piece_sum _ _ _ _
    _ ≤ ∑ j ∈ Finset.range (k+1), (e/125000^j%125000 : ℕ)*
        (C*(V : ℝ)*((125000^j : ℕ) : ℝ)^Parameters.tau) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (Shared50RecursiveRootExecution.rootBudget_bound j V) (Nat.cast_nonneg _)
    _ = C*(V : ℝ)*(∑ j ∈ Finset.range (k+1),
        (e/125000^j%125000 : ℕ)*((125000^j : ℕ) : ℝ)^Parameters.tau) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ C*(V : ℝ)*
        ((((125000 : ℝ)-1)*(125000 : ℝ)^Parameters.tau /
          ((125000 : ℝ)^Parameters.tau-1))*(e : ℝ)^Parameters.tau) :=
      mul_le_mul_of_nonneg_left
        (Swap.Recurrence.pieces_le (by decide) Shared50RecursiveBudgetBound.exponent_range.1
          (fun j => e/125000^j%125000) (fun j => Nat.mod_lt _ (by decide)) hk) hCV
    _ = constant*(V : ℝ)*(e : ℝ)^Parameters.tau := by
      unfold constant C
      ring

/-- Canonical integer-logarithm partition, with no chosen depth parameter. -/
theorem canonical_bound (V e : ℕ) (he : e ≠ 0) :
    ((depths 125000 e (Nat.log 125000 e)).map (fun j => (rootBudget j V : ℝ))).sum ≤
      constant*(V : ℝ)*(e : ℝ)^Parameters.tau :=
  sum_bound V e _ (Nat.pow_log_le_self _ he)

end
end IntegerMultBounds.Machine.ArbitraryWidthPieceBudget
