module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Ring

/-! Sum an executed schedule's shared, native-volume and arithmetic-volume bills.
No positivity premise is needed to assemble the pointwise inequalities. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

theorem sum_nat_cost_le_affine {α : Type} (cost shared volume work : α → ℕ)
    (c : ℕ) (D : ℝ) (xs : List α)
    (hcost : ∀ x ∈ xs, (cost x : ℝ) ≤ (shared x+c*volume x : ℕ)+D*(work x : ℕ)) :
    ((xs.map cost).sum : ℝ) ≤
      ((xs.map shared).sum+c*(xs.map volume).sum : ℕ)+D*((xs.map work).sum : ℕ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hcost x (by simp)
    have ht := ih (fun y hy => hcost y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    calc
      _ ≤ ((shared x+c*volume x : ℕ) : ℝ)+D*(work x : ℕ)+
          (((xs.map shared).sum+c*(xs.map volume).sum : ℕ)+D*((xs.map work).sum : ℕ)) := add_le_add hx ht
      _ = _ := by push_cast; ring

end IntegerMultBounds.MathlibTM2.Cost
