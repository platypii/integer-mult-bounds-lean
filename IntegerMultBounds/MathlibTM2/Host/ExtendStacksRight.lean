module

public import IntegerMultBounds.MathlibTM2.Host.ExtendStacks

/-! Ordinary metadata in an added spectator tape survives an embedded trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
variable {T T' A : ℕ}

theorem exec_extendStacks_right {Q : ℕ} {P P' U : Type} (h : T ≤ T')
    {ι : P → P'} {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q A U}
    (hbody : ∀ f, body' (ι f) = embProg (Fin.castLE h) ι (body f))
    {p : Pr P T Q A U} {v v₁ : HS T Q A U} {S S₁ : Stacks T A} {n : ℕ}
    (hex : Exec body p (mk v S) n (mk v₁ S₁))
    (j : Fin T') (hj : T ≤ j.val) (xs : List (Fin (A+4)))
    (v' : HS T' Q A U) (hv : embDn (Fin.castLE h) v' = v) :
    ∃ v₁', embDn (Fin.castLE h) v₁' = v₁ ∧ v₁'.user = v₁.user ∧
      Exec body' (embProg (Fin.castLE h) ι p)
        (mk v' {extendStacks h S with R := Function.update (extendStacks h S).R j xs}) n
        (mk v₁' {extendStacks h S₁ with R := Function.update (extendStacks h S₁).R j xs}) := by
  have hoff (i : Fin T') (hi : T ≤ i.val) : ∀ k : Fin T, Fin.castLE h k ≠ i := by
    intro k he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castLE] at hv
    omega
  let B : Stacks T' A := {extendStacks h S with R := Function.update (extendStacks h S).R j xs}
  have hviewB : embStk (Fin.castLE h) B = S := by
    rw [embStk_updateR_off _ _ _ (hoff j hj),embStk_extendStacks]
  obtain ⟨vf,F,he,hvf,hu,hview,hframe⟩ := exec_emb (Fin.castLE_injective h) hbody hex v' hv B hviewB
  have hF : F = {extendStacks h S₁ with R := Function.update (extendStacks h S₁).R j xs} := by
    refine Stacks.ext (congrArg (fun C : Stacks T A => C.inp) hview)
      (congrArg (fun C : Stacks T A => C.out) hview) ?_ ?_
    · funext i
      by_cases hi : i.val < T
      · have hf := congrArg (fun C : Stacks T A => C.L ⟨i.val,hi⟩) hview
        simpa [embStk,extendStacks,hi] using hf
      · have hf := (hframe i (hoff i (by omega))).1
        simpa [B,extendStacks,Function.update_apply,hi] using hf
    · funext i
      by_cases hi : i.val < T
      · have hne : i ≠ j := by intro heq; subst i; omega
        have hf := congrArg (fun C : Stacks T A => C.R ⟨i.val,hi⟩) hview
        simpa [embStk,extendStacks,hi,hne] using hf
      · have hf := (hframe i (hoff i (by omega))).2
        simpa [B,extendStacks,Function.update_apply,hi] using hf
  exact ⟨vf,hvf,hu,he.cast rfl (congrArg (mk vf) hF)⟩

end IntegerMultBounds.MathlibTM2.Host
