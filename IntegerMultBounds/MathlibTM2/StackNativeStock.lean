module

public import IntegerMultBounds.MathlibTM2.StackResources

/-! Guarded native loops reuse storage: a successful pop pays for a subsequent
push, and boundary stock is independent of the number of loop iterations. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Stack
variable {K : Type} {Γ : K → Type} {σ P : Type} [DecidableEq K] [Fintype K]

theorem mn_pop_one_push (s : Store Γ σ) (k : K) (f : σ → Option (Γ k) → σ)
    (a : Action Γ σ) (ha : mnActPush a ≤ 1) (hne : s.stk k ≠ []) :
    mnSize ((Action.pop k f a).run s) ≤ mnSize s := by
  have hp := mn_size_update s (f s.var (s.stk k).head?) k (s.stk k).tail
  have hs := mn_act_size a ⟨f s.var (s.stk k).head?,Function.update s.stk k (s.stk k).tail⟩
  have hl : (s.stk k).tail.length+1 = (s.stk k).length := by
    cases h : s.stk k with
    | nil => exact False.elim (hne h)
    | cons x xs => rfl
  change mnSize (a.run ⟨f s.var (s.stk k).head?,Function.update s.stk k (s.stk k).tail⟩) ≤ mnSize s
  omega

theorem loop_action_within (body : P → Prog P Γ σ) (a : Action Γ σ) (test : σ → Bool)
    (I : Store Γ σ → Prop)
    (hsafe : ∀ s, I s → test s.var = true → I (a.run s) ∧ mnSize (a.run s) ≤ mnSize s)
    {s t : Store Γ σ} {n : ℕ} (he : Exec body (.loop test (.act a)) s n t)
    (hI : I s) (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (.loop test (.act a)) s n t := by
  induction n using Nat.strong_induction_on generalizing s t with
  | h n ih =>
    cases he with
    | loop_false hf => exact .loop_false hf hb
    | @loop_true _ _ _ _ _ m k hf hp hq =>
      cases hp
      obtain ⟨hI',hg⟩ := hsafe s hI hf
      have ht := ih k (by omega) hq hI' (by omega)
      exact .loop_true hf (.act a s hb (by omega)) ht

end IntegerMultBounds.MathlibTM2.Fast.Main
