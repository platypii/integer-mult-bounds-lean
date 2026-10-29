module

public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Extend a register bank with blank workspace, preserving the original bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack

variable {T T' A : ℕ}

def extendStacks (_h : T ≤ T') (S : Stacks T A) : Stacks T' A :=
  ⟨S.inp,S.out,(fun i => if hi : i.val < T then S.L ⟨i.val,hi⟩ else []),
    (fun i => if hi : i.val < T then S.R ⟨i.val,hi⟩ else [])⟩

@[simp] theorem embStk_extendStacks (h : T ≤ T') (S : Stacks T A) :
    embStk (Fin.castLE h) (extendStacks h S) = S := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i; simp [embStk,extendStacks,i.isLt]
  · funext i; simp [embStk,extendStacks,i.isLt]

theorem extendStacks_fresh (h : T ≤ T') (S : Stacks T A) (i : Fin T') (hi : T ≤ i.val) :
    (extendStacks h S).L i = [] ∧ (extendStacks h S).R i = [] := by
  simp [extendStacks,show ¬ i.val < T by omega]

/-- A view and blank added registers determine the whole extended bank. -/
theorem eq_extendStacks (h : T ≤ T') (S : Stacks T A) (F : Stacks T' A)
    (hview : embStk (Fin.castLE h) F = S)
    (hfresh : ∀ i : Fin T', T ≤ i.val → F.L i = [] ∧ F.R i = []) :
    F = extendStacks h S := by
  refine Stacks.ext (congrArg (fun G : Stacks T A => G.inp) hview)
    (congrArg (fun G : Stacks T A => G.out) hview) ?_ ?_
  · funext i
    by_cases hi : i.val < T
    · have he := congrArg (fun G : Stacks T A => G.L ⟨i.val,hi⟩) hview
      simpa [embStk,extendStacks,hi] using he
    · simpa [extendStacks,hi] using (hfresh i (by omega)).1
  · funext i
    by_cases hi : i.val < T
    · have he := congrArg (fun G : Stacks T A => G.R ⟨i.val,hi⟩) hview
      simpa [embStk,extendStacks,hi] using he
    · simpa [extendStacks,hi] using (hfresh i (by omega)).2

/-- Execute in a larger blank bank, with exactly the original time and poststate. -/
theorem exec_extendStacks {Q : ℕ} {P P' U : Type} (h : T ≤ T')
    {ι : P → P'} {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q A U}
    (hbody : ∀ f, body' (ι f) = embProg (Fin.castLE h) ι (body f))
    {p : Pr P T Q A U} {v v₁ : HS T Q A U} {S S₁ : Stacks T A} {n : ℕ}
    (hex : Exec body p (mk v S) n (mk v₁ S₁))
    (v' : HS T' Q A U) (hv : embDn (Fin.castLE h) v' = v) :
    ∃ v₁', embDn (Fin.castLE h) v₁' = v₁ ∧ v₁'.user = v₁.user ∧
      Exec body' (embProg (Fin.castLE h) ι p) (mk v' (extendStacks h S)) n
        (mk v₁' (extendStacks h S₁)) := by
  have hinj : Function.Injective (Fin.castLE h) := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin T' => k.val) hij
  obtain ⟨v₁',F,he,hv₁,hu,hview,hframe⟩ := exec_emb hinj hbody hex v' hv
    (extendStacks h S) (embStk_extendStacks h S)
  have hF : F = extendStacks h S₁ := eq_extendStacks h S₁ F hview (by
    intro i hi
    have hoff : ∀ j : Fin T, Fin.castLE h j ≠ i := by
      intro j hij
      have heq := congrArg Fin.val hij
      have hj := j.isLt
      simp only [Fin.val_castLE] at heq
      omega
    have hf := hframe i hoff
    have hb := extendStacks_fresh h S i hi
    exact ⟨hf.1.trans hb.1,hf.2.trans hb.2⟩)
  exact ⟨v₁',hv₁,hu,by simpa only [hF] using he⟩

/-- Allocating a prefix in the original bank commutes with adding workspace. -/
theorem extendStacks_updateR (h : T ≤ T') (S : Stacks T A) (i : Fin T) (xs : List (Fin (A+4))) :
    extendStacks h {S with R := Function.update S.R i xs} =
      {extendStacks h S with R := Function.update (extendStacks h S).R (Fin.castLE h i) xs} := by
  have hinj : Function.Injective (Fin.castLE h) := by
    intro i j he
    apply Fin.ext
    exact congrArg (fun k : Fin T' => k.val) he
  symm
  apply eq_extendStacks h
  · rw [embStk_updateR hinj,embStk_extendStacks]
  · intro j hj
    have hn : j ≠ Fin.castLE h i := by
      intro he
      have hh := congrArg Fin.val he
      have hi := i.isLt
      simp only [Fin.val_castLE] at hh
      omega
    have hf := extendStacks_fresh h S j hj
    exact ⟨hf.1,by simpa only [Function.update_of_ne hn] using hf.2⟩

end IntegerMultBounds.MathlibTM2.Host
