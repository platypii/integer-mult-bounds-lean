module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Repeated overrides on one embedded bank compose without retaining intermediate backgrounds. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.MathlibTM2.Stack

theorem embOvr_overwrite {T T' A : ℕ} (e : Fin T → Fin T')
    (F G : Stacks T A) (S : Stacks T' A) :
    embOvr e F.get (embOvr e G.get S) = embOvr e F.get S := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    simp only [embOvr,Stacks.get,embExt]
    cases embInv e i <;> rfl
  · funext i
    simp only [embOvr,Stacks.get,embExt]
    cases embInv e i <;> rfl

/-- Project an owned physical update back to its logical tape. -/
theorem embStk_update_right {T T' A : ℕ} (e : Fin T → Fin T')
    (he : Function.Injective e) (S : Stacks T' A) (i : Fin T) (xs : List (Fin (A+4))) :
    embStk e {S with R := Function.update S.R (e i) xs} =
      {embStk e S with R := Function.update (embStk e S).R i xs} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext j
  by_cases h : j = i
  · subst j; simp [embStk,Function.comp_def]
  · have he' : e j ≠ e i := fun h' => h (he h')
    simp [embStk,Function.comp_def,h,he']

end IntegerMultBounds.MathlibTM2.Host
