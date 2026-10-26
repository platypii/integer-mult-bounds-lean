module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedComponentInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingHeaderWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyReady

/-! Prepare both components from a released real-solver bank and restore its readiness. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def preparedComponentInputs : Pr P₀ 148 Q A U :=
  .seq (embProg componentReg id couplingHeaderWidth) (.seq retainedComponentInputs (uclear 94))

def preparedComponentInputsCost (q s : ℕ) : ℕ := retainedComponentInputsCost s (2*q+8)+12*q+27

theorem preparedComponentInputs_exec {P N q l s t u band : ℕ} [NeZero s]
    (hA : 4 ≤ A) (B : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady P N q l s t u band 0 0
      (cstream A (2*q+8) (chirpLine s B)++tail) (embStk componentReg S))
    (h147 : S.R 147 = []) :
    let X := cstream A (2*q+8) ((chirpLine s B).map realPartWord)++tail
    let Y := cstream A (2*q+8) ((chirpLine s B).map imagPartWord)++S.R 144
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedComponentInputsCost q s ∧
      Exec (embTab componentReg body) preparedComponentInputs (mk v S) n
        (mk v' {S with R := Function.update (Function.update S.R 110 X) 144 Y}) ∧
      LengthKeyReady P N q l s t u band 0 0 X
        (embStk componentReg {S with R := Function.update (Function.update S.R 110 X) 144 Y}) := by
  dsimp only
  let X := cstream A (2*q+8) ((chirpLine s B).map realPartWord)++tail
  let Y := cstream A (2*q+8) ((chirpLine s B).map imagPartWord)++S.R 144
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  have h94 : S.R 94 = [] := by simpa [embStk,componentReg] using hready.blank 94 (by decide) (by decide) (by decide)
  have hfresh (r : Fin 144) (hr : r ∈ [(131 : Fin 144),134,135,136,137,140]) : S.R (componentReg r) = [] :=
    hready.fresh r hr
  obtain ⟨v₁,hu₁,he₁⟩ := couplingHeaderWidth_exec (body := body) q (embDn componentReg v) (embStk componentReg S)
    (by simpa [embStk,componentReg] using hq) (by simpa [embStk,componentReg] using h94)
    (hfresh 135 (by simp))
  have hbody : ∀ p, (embTab componentReg body) (id p) = embProg componentReg id (body p) := fun _ => rfl
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := id) (body' := embTab componentReg body)
    componentReg_injective hbody he₁ v rfl S rfl
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 94 (List.replicate (2*q+8) tick)}
  have he₂' : Exec (embTab componentReg body) (embProg componentReg id couplingHeaderWidth)
      (mk v S) (8*q+9) (mk v₂ S₁) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    rw [embOvr_updR componentReg_injective (embStk componentReg S) S 94 (List.replicate (2*q+8) tick),embOvr_stk]
    rfl
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := retainedComponentInputs_exec (body := body) hA s (2*q+8) (chirpLine s B)
    (by simp [chirpLine]) tail v₂ S₁ (by simpa [S₁] using hs) (by simp [S₁])
    (by simpa [S₁,embStk,componentReg] using hready.source)
    (by simpa [S₁,componentReg] using hfresh 131 (by simp))
    (by simpa [S₁,componentReg] using hfresh 134 (by simp))
    (by simpa [S₁,componentReg] using hfresh 135 (by simp))
    (by simpa [S₁,componentReg] using hfresh 136 (by simp))
    (by simpa [S₁,componentReg] using hfresh 137 (by simp)) (by simpa [S₁] using h147)
  let S₂ : Stacks 148 A := {S₁ with R := Function.update (Function.update S₁.R 110 X) 144 Y}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := embTab componentReg body) 94 v₃ S₂
  refine ⟨v₄,(8*q+9)+(n₃+(2*(2*q+8)+2)),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₂' (Exec.seq he₃ he₄)).cast ?_ ?_,?_⟩
  · dsimp [preparedComponentInputsCost]
    omega
  · simp [S₂,S₁]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h94' : k = 94 <;> by_cases h110 : k = 110 <;> by_cases h144 : k = 144 <;>
      simp [S₂,S₁,h94',h110,h144,h94,X,Y]
  · have hdrop : embStk componentReg {S with R := Function.update (Function.update S.R 110 X) 144 Y} =
        embStk componentReg {S with R := Function.update S.R 110 X} :=
      componentProject_updateR {S with R := Function.update S.R 110 X} 144 Y (by decide)
    rw [hdrop]
    have hproject : embStk componentReg {S with R := Function.update S.R 110 X} =
        {(embStk componentReg S) with R := Function.update (embStk componentReg S).R 110 X} := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hk : k = 110
      · subst k; simp [embStk,componentReg]
      · have hne : componentReg k ≠ 110 := by intro he; apply hk; apply Fin.ext; exact congrArg (fun r : Fin 148 => r.val) he
        simp [embStk,Function.comp_def,hk,hne]
    rw [hproject]
    exact hready.update_source X

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
