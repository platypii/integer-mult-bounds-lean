module

public import IntegerMultBounds.MathlibTM2.Host.Embed

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
variable {T T' A : ℕ}

/-- Reading an injectively placed bank transports an update at one placed register. -/
theorem embStk_updateR {e : Fin T → Fin T'} (he : Function.Injective e)
    (S : Stacks T' A) (x : Fin T) (xs : List (Fin (A+4))) :
    embStk e {S with R := Function.update S.R (e x) xs} =
      {embStk e S with R := Function.update (embStk e S).R x xs} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext j
  by_cases hj : j = x
  · subst j; simp [embStk]
  · simp [embStk,Function.comp_apply,Function.update_of_ne (he.ne hj),Function.update_of_ne hj]

/-- A write outside a placed bank leaves its entire view unchanged. -/
theorem embStk_updateR_off {e : Fin T → Fin T'} (S : Stacks T' A)
    (x : Fin T') (xs : List (Fin (A+4))) (hx : ∀ i, e i ≠ x) :
    embStk e {S with R := Function.update S.R x xs} = embStk e S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  simp only [embStk, Function.comp_apply, Function.update_of_ne (hx i)]

/-- Transport two sequential writes without expanding the intermediate bank. -/
theorem embOvr_updateR_updateR {e : Fin T → Fin T'} (he : Function.Injective e)
    (S : Stacks T' A) (x y : Fin T) (xs ys : List (Fin (A+4))) :
    embOvr e {embStk e S with R :=
      (Function.update (Function.update (embStk e S).R x xs) y ys)}.get S =
      {S with R := (Function.update (Function.update S.R (e x) xs) (e y) ys)} := by
  let B := embStk e S
  let B₁ : Stacks T A := {B with R := Function.update B.R x xs}
  change embOvr e {B₁ with R := Function.update B₁.R y ys}.get S = _
  rw [embOvr_updR he]
  dsimp only [B₁,B]
  rw [embOvr_updR he,embOvr_stk]

/-- Overriding only the placed right bank leaves every left stack unchanged. -/
theorem embOvr_right_left {e : Fin T → Fin T'} (S : Stacks T' A) (R : Fin T → List (Fin (A+4))) :
    (embOvr e {embStk e S with R := R}.get S).L = S.L := by
  change (embOvr e (embStk e S).get S).L = S.L
  rw [embOvr_stk]

theorem embOvr_left_of_eq {e : Fin T → Fin T'} (S : Stacks T' A) (B : Stacks T A)
    (hL : B.L = (embStk e S).L) : (embOvr e B.get S).L = S.L := by
  change embExt e B.L S.L = S.L
  rw [hL]
  exact congrArg Stacks.L (embOvr_stk (e := e) S)

end IntegerMultBounds.MathlibTM2.Host
