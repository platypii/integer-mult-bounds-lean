import IntegerMultBounds.Machine.Shared50RecursiveBudget
import IntegerMultBounds.Swap.Recurrence
import IntegerMultBounds.Shared50Parameters
import Mathlib.Data.Nat.Cast.Order.Field

/-! Analytic bound for the concrete natural recursive budget. The exact fixed
Shared50 branching count and World count give the certified exponent saving;
natural floor division only decreases the bound. This module bounds the budget,
not the execution time of a machine whose trace has not yet been established. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveBudgetBound
noncomputable section
open Networks
open Shared50TapeGlobal (roleCount)
open Shared50RecursiveBudget (base node budget)
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)
attribute [local irreducible] Shared50PieceSchedule.pieces Shared50RecursiveCallLayout.parked
  Shared50RecursiveBudget.base Shared50RecursiveBudget.node

/-- Real normalized recurrence for the actual compile-time coefficients. -/
def normalized (k : ℕ) : ℕ → ℝ
  | 0 => base k
  | depth+1 => (Shared50Parameters.s : ℝ)/roleCount*normalized k depth+node k

theorem normalized_nonneg (k depth : ℕ) : 0 ≤ normalized k depth := by
  induction depth with
  | zero => exact Nat.cast_nonneg _
  | succ depth ih =>
    exact add_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ih) (Nat.cast_nonneg _)

/-- Natural quotients introduce no extra cost, even for zero or nondivisible
volumes. No operation-count or recursive-machine premise is used. -/
theorem budget_le_normalized (k depth V : ℕ) : (budget k depth V : ℝ) ≤ normalized k depth*V := by
  induction depth generalizing V with
  | zero => simp only [budget,normalized,Nat.cast_mul]; exact le_rfl
  | succ depth ih =>
    have hdiv : ((V/roleCount : ℕ) : ℝ) ≤ (V : ℝ)/roleCount := Nat.cast_div_le
    calc
      (budget k (depth+1) V : ℝ) = (node k : ℝ)*V+Shared50Parameters.s*(budget k depth (V/roleCount) : ℝ) := by
        simp only [budget,Nat.cast_add,Nat.cast_mul]
      _ ≤ (node k : ℝ)*V+Shared50Parameters.s*(normalized k depth*((V/roleCount : ℕ) : ℝ)) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (ih _) (Nat.cast_nonneg _))
      _ ≤ (node k : ℝ)*V+Shared50Parameters.s*(normalized k depth*((V : ℝ)/roleCount)) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdiv (normalized_nonneg k depth)) (Nat.cast_nonneg _))
      _ = normalized k (depth+1)*V := by rw [normalized]; ring

/-- The exponent of width retains the fixed certified positive saving. -/
theorem exponent_range : 0 < Parameters.tau ∧ Parameters.tau < 1 := by
  norm_num [Parameters.tau]

theorem exponent_saving : 1-Parameters.tau = 296/(10^11 : ℝ) := by
  unfold Parameters.tau
  ring

theorem branching_bound : (Shared50Parameters.s : ℝ)/roleCount ≤ (125000 : ℝ)^Parameters.tau := by
  rw [Shared50RecursiveNodeLayout.roleCount_eq_W]
  exact Shared50Parameters.branching_bound.le

/-- One fixed constant for a fixed compiled return-address capacity, independent
of depth, runtime width, spectators, payload volume and previous stack contents. -/
def constant (k : ℕ) : ℝ :=
  ((base k : ℝ)+(node k : ℝ))*(125000 : ℝ)^Parameters.tau /
    ((125000 : ℝ)^Parameters.tau-1)

theorem constant_positive (k : ℕ) : 0 < constant k := by
  have hx : 1 < (125000 : ℝ)^Parameters.tau := Real.one_lt_rpow (by norm_num) exponent_range.1
  have hb : 0 < base k := by
    unfold Shared50RecursiveBudget.base
    omega
  have hb' : (0 : ℝ) < base k := by exact_mod_cast hb
  have hn : (0 : ℝ) ≤ node k := Nat.cast_nonneg _
  unfold constant
  exact div_pos (mul_pos (by linarith) (by linarith)) (by linarith)

theorem normalized_bound (k depth : ℕ) :
    normalized k depth ≤ constant k*((125000^depth : ℕ) : ℝ)^Parameters.tau := by
  exact Swap.Recurrence.power_width_bound (F := normalized k) (m := 125000)
    (a := (Shared50Parameters.s : ℝ)/roleCount) (L := (base k : ℝ)) (C := (node k : ℝ))
    (by decide) exponent_range.1 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    branching_bound (Nat.cast_nonneg _) (Nat.cast_nonneg _) le_rfl (fun _ => le_rfl) depth

/-- Budget-only power-width bound with the manuscript's certified exponent,
including every fixed node/entry/recovery/return coefficient already in budget. -/
theorem power_width_bound (k depth V : ℕ) :
    (budget k depth V : ℝ) ≤ constant k*(V : ℝ)*((125000^depth : ℕ) : ℝ)^Parameters.tau := by
  calc
    (budget k depth V : ℝ) ≤ normalized k depth*V := budget_le_normalized k depth V
    _ ≤ (constant k*((125000^depth : ℕ) : ℝ)^Parameters.tau)*V :=
      mul_le_mul_of_nonneg_right (normalized_bound k depth) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The same bound uses the actual runtime descriptor width and logical volume.
Proving an execution takes at most this budget remains a separate obligation. -/
theorem descriptor_bound {depth : ℕ} {v : Descriptor} (k : ℕ)
    (h : Shared50RecursiveDepth.Shape depth v) :
    (budget k depth (volume prime v) : ℝ) ≤
      constant k*(volume prime v : ℝ)*(v.width : ℝ)^Parameters.tau := by
  rw [h.width]
  exact power_width_bound k depth (volume prime v)

/-- Uniform real bound, with no free schedule/count assumptions. -/
theorem exists_uniform_bound (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ depth V : ℕ,
    (budget k depth V : ℝ) ≤ C*(V : ℝ)*((125000^depth : ℕ) : ℝ)^(1-296/(10^11 : ℝ)) :=
  ⟨constant k,constant_positive k,power_width_bound k⟩

end
end IntegerMultBounds.Machine.Shared50RecursiveBudgetBound
