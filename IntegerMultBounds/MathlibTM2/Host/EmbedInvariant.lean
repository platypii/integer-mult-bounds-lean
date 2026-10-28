module

public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.StackInvariant

/-! Register placement preserves invariants throughout every intermediate store. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
variable {T T' Q A : ℕ} {U P P' : Type} {e : Fin T → Fin T'}
  (he : Function.Injective e) {ι : P → P'}
  {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q A U}
  (hbody : ∀ f, body' (ι f) = embProg e ι (body f))
  (B : Stacks T' A)
  {Inv : ℕ → Store (HΓ (T := T) A) (HS T Q A U) → Prop}
  {J : ℕ → Store (HΓ (T := T') A) (HS T' Q A U) → Prop}
  (hInv : ∀ d s w, embDn e w = s.var → Inv d s →
    J d ⟨w,(embOvr e s.stk B).get⟩) {d : ℕ}
include he hbody hInv

theorem embProg_execWithin {p : Pr P T Q A U}
    {s t : Store (HΓ (T := T) A) (HS T Q A U)} {n : ℕ} (h : ExecWithin body Inv d p s n t) :
    ∀ w : HS T' Q A U, embDn e w = s.var → ∃ w', embDn e w' = t.var ∧
      ExecWithin body' J d (embProg e ι p) ⟨w, (embOvr e s.stk B).get⟩ n ⟨w', (embOvr e t.stk B).get⟩ := by
  induction h with
  | @act d a s hi ho =>
      intro w hw
      obtain ⟨w', hw', hr⟩ := embAct_run he B a s w hw
      have hstart := hInv d s w hw hi
      have hend := hInv d (a.run s) w' hw' ho
      have ht : ExecWithin body' J d (.act (embAct e a))
          ⟨w,(embOvr e s.stk B).get⟩ 1 ((embAct e a).run ⟨w,(embOvr e s.stk B).get⟩) :=
        .act _ _ hstart (by rw [hr]; exact hend)
      exact ⟨w',hw',hr ▸ ht⟩
  | seq _ _ ihp ihq =>
      intro w hw
      obtain ⟨w₁, hw₁, h₁⟩ := ihp w hw
      obtain ⟨w₂, hw₂, h₂⟩ := ihq w₁ hw₁
      exact ⟨w₂, hw₂, ExecWithin.seq h₁ h₂⟩
  | @cond_true d f p q s t n hf _ ih =>
      intro w hw
      obtain ⟨w', hw', h'⟩ := ih w hw
      exact ⟨w', hw', ExecWithin.cond_true (f := fun w => f (embDn e w))
        (show f (embDn e w) = true by rw [hw]; exact hf) h'⟩
  | @cond_false d f p q s t n hf _ ih =>
      intro w hw
      obtain ⟨w', hw', h'⟩ := ih w hw
      exact ⟨w', hw', ExecWithin.cond_false (f := fun w => f (embDn e w))
        (show f (embDn e w) = false by rw [hw]; exact hf) h'⟩
  | @loop_false d f p s hf hi =>
      intro w hw
      exact ⟨w, hw, ExecWithin.loop_false (f := fun w => f (embDn e w))
        (show f (embDn e w) = false by rw [hw]; exact hf) (hInv d s w hw hi)⟩
  | @loop_true d f p s t u m n hf _ _ ihp ihl =>
      intro w hw
      obtain ⟨w₁, hw₁, h₁⟩ := ihp w hw
      obtain ⟨w₂, hw₂, h₂⟩ := ihl w₁ hw₁
      exact ⟨w₂, hw₂, ExecWithin.loop_true (f := fun w => f (embDn e w))
        (show f (embDn e w) = true by rw [hw]; exact hf) h₁ h₂⟩
  | @call d f s t n hi _ ho ih =>
      intro w hw
      obtain ⟨w', hw', h'⟩ := ih w hw
      refine ⟨w', hw', ExecWithin.call (hInv d s w hw hi) ?_ (hInv d t w' hw' ho)⟩
      rw [hbody]
      exact h'


end IntegerMultBounds.MathlibTM2.Host
