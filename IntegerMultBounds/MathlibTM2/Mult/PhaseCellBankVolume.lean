module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- Replacing one placed word increases bank volume by at most its new length. -/
theorem bank_volume_update_le {I J α : Type*} [Fintype I] [DecidableEq J]
    (ι : I → J) (hι : Function.Injective ι) (R : J → List α) (x : I) (ys : List α) :
    (∑ j, (Function.update R (ι x) ys (ι j)).length) ≤ (∑ j, (R (ι j)).length)+ys.length := by
  classical
  calc
    _ ≤ ∑ j, ((R (ι j)).length+if j = x then ys.length else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases he : j = x
      · subst j; simp
      · simp only [Function.update_of_ne (hι.ne he),ite_eq_right he,Nat.add_zero,Nat.le_refl]
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Filling distinct initially empty slots adds exactly the volume of the new
words to a finite bank. All other slots are framed. -/
theorem bank_volume_of_frame {I J α : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (slot : J → I) (hslot : Function.Injective slot)
    (R F : I → List α) (words : J → List α)
    (hblank : ∀ j, R (slot j) = []) (hwords : ∀ j, F (slot j) = words j)
    (hoff : ∀ i, (∀ j, slot j ≠ i) → F i = R i) :
    (∑ i, (F i).length) = (∑ i, (R i).length)+(∑ j, (words j).length) := by
  classical
  have hpoint (i : I) : (F i).length = (R i).length +
      ∑ j, if slot j = i then (words j).length else 0 := by
    by_cases hi : ∃ j, slot j = i
    · obtain ⟨j,rfl⟩ := hi
      simp [hwords,hblank,hslot.eq_iff]
    · have hi' : ∀ j, slot j ≠ i := by simpa using hi
      simp [hoff i hi',hi']
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
