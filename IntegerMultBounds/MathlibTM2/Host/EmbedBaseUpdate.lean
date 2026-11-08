module

public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Writes inside an overridden bank do not affect the surrounding frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
variable {T T' A : ℕ}

theorem embOvr_base_updateR (e : Fin T → Fin T')
    (f : ∀ k : HK T, List (HΓ A k)) (S : Stacks T' A) (x : Fin T) (xs : List (Fin (A+4))) :
    embOvr e f {S with R := Function.update S.R (e x) xs} = embOvr e f S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext j
  simp only [embOvr,embExt]
  cases hj : embInv e j with
  | none => simp [Function.update_of_ne (embInv_none hj x).symm]
  | some i => rfl

end IntegerMultBounds.MathlibTM2.Host
