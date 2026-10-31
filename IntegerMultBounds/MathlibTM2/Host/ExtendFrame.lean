module

public import IntegerMultBounds.MathlibTM2.Host.ExtendStacks

/-! Carry blank surrounding workspace through an executed smaller bank setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack
variable {k n m T A : ℕ}

theorem embStk_prefix_eq (h : n ≤ m) (small : Fin n → Fin T) (large : Fin m → Fin T)
    (hprefix : ∀ i, large (Fin.castLE h i) = small i) (S : Stacks T A) :
    embStk (Fin.castLE h) (embStk large S) = embStk small S := by
  refine Stacks.ext rfl rfl ?_ ?_
  all_goals funext i; simp only [embStk,Function.comp_apply,hprefix]

theorem embStk_extend_prefix (hkn : k ≤ n) (hnm : n ≤ m) (S : Stacks k A) :
    embStk (Fin.castLE hnm) (extendStacks (hkn.trans hnm) S) = extendStacks hkn S := by
  refine Stacks.ext rfl rfl ?_ ?_
  all_goals funext i; simp [embStk,extendStacks]

theorem embStk_extend_of_frame (h : n ≤ m) (small : Fin n → Fin T) (large : Fin m → Fin T)
    (hlarge : Function.Injective large) (hprefix : ∀ i, large (Fin.castLE h i) = small i)
    (S F : Stacks T A) (B : Stacks n A)
    (hview : embStk small F = B)
    (hblank : ∀ i : Fin m, n ≤ i.val → S.L (large i) = [] ∧ S.R (large i) = [])
    (hleft : F.L = S.L) (hframe : ∀ i, (∀ j, i ≠ small j) → F.R i = S.R i) :
    embStk large F = extendStacks h B := by
  apply eq_extendStacks h B
  · rw [embStk_prefix_eq h small large hprefix,hview]
  · intro i hi
    have hoff : ∀ j, large i ≠ small j := by
      intro j he
      rw [← hprefix j] at he
      have hv := congrArg Fin.val (hlarge he)
      have hj := j.isLt
      change i.val = j.val at hv
      omega
    exact ⟨(congrFun hleft (large i)).trans (hblank i hi).1,
      (hframe _ hoff).trans (hblank i hi).2⟩

end IntegerMultBounds.MathlibTM2.Host
