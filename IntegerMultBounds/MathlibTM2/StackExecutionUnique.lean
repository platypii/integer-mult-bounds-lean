module

public import IntegerMultBounds.MathlibTM2.Stack

/-! The structured semantics determines both the step count and final store. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Stack
variable {K : Type} {Γ : K → Type} {σ P : Type} [DecidableEq K]
  {body : P → Prog P Γ σ} {p : Prog P Γ σ} {s t : Store Γ σ} {m : ℕ}

theorem Exec.unique (h : Exec body p s m t) :
    ∀ {n u}, Exec body p s n u → m = n ∧ t = u := by
  induction h with
  | act a s => intro n u g; cases g; exact ⟨rfl,rfl⟩
  | seq _ _ ihp ihq =>
    intro n u g
    cases g with
    | seq gp gq =>
      obtain ⟨hm,ht⟩ := ihp gp
      subst ht
      obtain ⟨hn,hu⟩ := ihq gq
      exact ⟨by omega,hu⟩
  | cond_true hf _ ih =>
    intro n u g
    cases g with
    | cond_true _ gp => obtain ⟨hn,hu⟩ := ih gp; exact ⟨by omega,hu⟩
    | cond_false hg _ => simp [hf] at hg
  | cond_false hf _ ih =>
    intro n u g
    cases g with
    | cond_false _ gp => obtain ⟨hn,hu⟩ := ih gp; exact ⟨by omega,hu⟩
    | cond_true hg _ => simp [hf] at hg
  | loop_false hf =>
    intro n u g
    cases g with
    | loop_false _ => exact ⟨rfl,rfl⟩
    | loop_true hg _ _ => simp [hf] at hg
  | loop_true hf _ _ ihp ihq =>
    intro n u g
    cases g with
    | loop_false hg => simp [hf] at hg
    | loop_true _ gp gq =>
      obtain ⟨hm,ht⟩ := ihp gp
      subst ht
      obtain ⟨hn,hu⟩ := ihq gq
      exact ⟨by omega,hu⟩
  | call _ ih =>
    intro n u g
    cases g with
    | call gp => obtain ⟨hn,hu⟩ := ih gp; exact ⟨by omega,hu⟩

end IntegerMultBounds.MathlibTM2.Stack
