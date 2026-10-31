module

public import IntegerMultBounds.MathlibTM2.StackInvariant

/-! Lift an existing loop execution using an invariant at iteration boundaries.
The trace invariant can include reusable scratch absent from the boundary. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Stack
variable {K : Type} {Γ : K → Type} {σ P : Type} [DecidableEq K]

theorem loop_within_of_boundary (body : P → Prog P Γ σ) (p : Prog P Γ σ) (test : σ → Bool)
    (I : Store Γ σ → Prop) (J : ℕ → Store Γ σ → Prop) (depth : ℕ)
    (hIJ : ∀ s, I s → J depth s)
    (hstep : ∀ s t n, I s → test s.var = true → Exec body p s n t →
      ExecWithin body J depth p s n t ∧ I t)
    {s t : Store Γ σ} {n : ℕ} (he : Exec body (.loop test p) s n t) (hs : I s) :
    ExecWithin body J depth (.loop test p) s n t := by
  induction n using Nat.strong_induction_on generalizing s t with
  | h n ih =>
    cases he with
    | loop_false hf => exact .loop_false hf (hIJ s hs)
    | @loop_true _ _ _ _ _ m k hf hp hq =>
      obtain ⟨hw,ht⟩ := hstep _ _ _ hs hf hp
      exact .loop_true hf hw (ih k (by omega) hq ht)

end IntegerMultBounds.MathlibTM2.Stack
