module

public import IntegerMultBounds.MathlibTM2.StackInvariant

/-! Reuse an execution after changing state that its first action overwrites. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Stack
variable {K σ P : Type} {Γ : K → Type} [DecidableEq K]

inductive FirstAction (a : Action Γ σ) : Prog P Γ σ → Prop
  | act : FirstAction a (.act a)
  | seq {p q} : FirstAction a p → FirstAction a (.seq p q)

theorem FirstAction.change_start {a : Action Γ σ} {p : Prog P Γ σ} (hfirst : FirstAction a p)
    {body : P → Prog P Γ σ} {Inv : ℕ → Store Γ σ → Prop} {depth n : ℕ} {s s' t : Store Γ σ}
    (he : ExecWithin body Inv depth p s n t) (hInv : Inv depth s') (ha : a.run s' = a.run s) :
    ExecWithin body Inv depth p s' n t := by
  induction hfirst generalizing s s' t n with
  | act =>
    cases he with
    | act _ _ hstart hend =>
      exact (ExecWithin.act a s' hInv (ha.symm ▸ hend)).cast rfl ha
  | seq hfirst ih =>
    cases he with
    | seq hp hq => exact .seq (ih hp hInv ha) hq

end IntegerMultBounds.MathlibTM2.Stack
