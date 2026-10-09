import IntegerMultBounds.Machine.ArbitrarySliceStep
import IntegerMultBounds.Machine.ArbitraryWidthPieceBudget

/-! The fully paid slice step, including preparation, header restoration and
offset advancement, retains the certified sublinear width exponent. -/
namespace IntegerMultBounds.Machine.ArbitrarySliceStepBudget
noncomputable section
open Networks

def budget (depth V : ℕ) := Shared50RecursiveRootExecution.rootBudget depth V+1087*V

theorem cost_le (depth V b : ℕ) (ts bs : List Bool) (hV : 0 < V) (hb : b ≤ V)
    (ht : ts.length ≤ 2*V) (hs : bs.length ≤ 2*V) :
    ArbitrarySliceStep.cost depth V b ts bs ≤ budget depth V := by
  unfold ArbitrarySliceStep.cost budget
  omega

def coefficient : ℝ := Shared50RecursiveRootExecution.constant+1087

theorem coefficient_positive : 0 < coefficient := by
  have h := Shared50RecursiveRootExecution.constant_positive
  unfold coefficient
  linarith

theorem budget_bound (depth V : ℕ) :
    (budget depth V : ℝ) ≤ coefficient*V*((125000^depth : ℕ) : ℝ)^Parameters.tau := by
  have hr := Shared50RecursiveRootExecution.rootBudget_bound depth V
  have hw : (1 : ℝ) ≤ ((125000^depth : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ (125000 : ℕ)^depth from Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
  have hp := Real.one_le_rpow hw Shared50RecursiveBudgetBound.exponent_range.1.le
  have hv : (0 : ℝ) ≤ V := Nat.cast_nonneg _
  simp only [budget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,coefficient]
  nlinarith

def constant : ℝ := coefficient*
  (((125000 : ℝ)-1)*(125000 : ℝ)^Parameters.tau / ((125000 : ℝ)^Parameters.tau-1))

theorem constant_positive : 0 < constant := by
  have hx : 1 < (125000 : ℝ)^Parameters.tau :=
    Real.one_lt_rpow (by norm_num) Shared50RecursiveBudgetBound.exponent_range.1
  unfold constant
  exact mul_pos coefficient_positive
    (div_pos (mul_pos (by norm_num) (by linarith)) (by linarith))

theorem sum_bound (V e k : ℕ) (hk : 125000^k ≤ e) :
    ((ArbitraryWidthPieces.depths 125000 e k).map (fun j => (budget j V : ℝ))).sum ≤
      constant*V*(e : ℝ)^Parameters.tau := by
  have hCV : 0 ≤ coefficient*(V : ℝ) := mul_nonneg coefficient_positive.le (Nat.cast_nonneg _)
  calc
    _ = ∑ j ∈ Finset.range (k+1), (e/125000^j%125000 : ℕ)*(budget j V : ℝ) :=
      ArbitraryWidthPieces.real_piece_sum _ _ _ _
    _ ≤ ∑ j ∈ Finset.range (k+1), (e/125000^j%125000 : ℕ)*
        (coefficient*(V : ℝ)*((125000^j : ℕ) : ℝ)^Parameters.tau) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (budget_bound j V) (Nat.cast_nonneg _)
    _ = coefficient*(V : ℝ)*(∑ j ∈ Finset.range (k+1),
        (e/125000^j%125000 : ℕ)*((125000^j : ℕ) : ℝ)^Parameters.tau) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ coefficient*(V : ℝ)*
        ((((125000 : ℝ)-1)*(125000 : ℝ)^Parameters.tau /
          ((125000 : ℝ)^Parameters.tau-1))*(e : ℝ)^Parameters.tau) :=
      mul_le_mul_of_nonneg_left
        (Swap.Recurrence.pieces_le (by decide) Shared50RecursiveBudgetBound.exponent_range.1
          (fun j => e/125000^j%125000) (fun j => Nat.mod_lt _ (by decide)) hk) hCV
    _ = constant*V*(e : ℝ)^Parameters.tau := by unfold constant; ring

end
end IntegerMultBounds.Machine.ArbitrarySliceStepBudget
