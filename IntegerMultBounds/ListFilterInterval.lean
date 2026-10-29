module

public import Mathlib.Data.List.Range
public import Lean.Elab.Tactic.Omega

/-! Filtering a supported predicate commutes with cropping its enclosing interval. -/

@[expose] public section
namespace List

/-- Cropping away unselected entries preserves a filtered list and its order. -/
theorem filter_take_drop_of_support {α : Type*} (xs : List α) (p : α → Bool)
    (a N : ℕ)
    (hsupport : ∀ j (hj : j < xs.length), p xs[j] = true → a ≤ j ∧ j < a+N) :
    ((xs.drop a).take N).filter p = xs.filter p := by
  have hleft : (xs.take a).filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx hp
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
    have hj' : j < xs.length := by simp only [List.length_take] at hj; omega
    have hb := hsupport j hj' (by simpa only [List.getElem_take] using hp)
    simp only [List.length_take] at hj
    omega
  have hright : (xs.drop (a+N)).filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx hp
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
    have hj' : a+N+j < xs.length := by simp only [List.length_drop] at hj; omega
    have hb := hsupport (a+N+j) hj' (by simpa only [List.getElem_drop] using hp)
    omega
  have hsplit : xs.take a ++ ((xs.drop a).take N ++ xs.drop (a+N)) = xs := by
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have hh := congrArg (List.filter p) hsplit
  simpa only [List.filter_append,hleft,hright,List.nil_append,List.append_nil] using hh

end List
