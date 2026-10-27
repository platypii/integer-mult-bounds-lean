module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageOriginalInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBoundaryResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalOriginalComponentInputs

/-! Preserve and split the ordinary complex input while retaining the computed shared pages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 263 Q A U}

def familyOriginalComponentInputs : Pr P₀ 263 Q A U :=
  embProg familyBoundaryReg Empty.elim (sharedPageOriginalComponentInputs (P₀ := Empty))

theorem familyOriginalComponentInputs_exec {P N q l s t u band : ℕ} [NeZero s]
    (hA : 4 ≤ A) (F : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 263 Q A U) (S : Stacks 263 A)
    (hready : LengthKeyReady P N q l s t u band 0 0
      (cstream A (2*q+8) (chirpLine s F)++tail) (embStk familyCouplingSourceReg S))
    (h147 : S.R 147 = []) :
    let X := cstream A (2*q+8) (chirpLine s (fun i => realPartWord (F i)))++tail
    let Y := cstream A (2*q+8) (chirpLine s (fun i => imagPartWord (F i)))++S.R 144
    let O := cstream A (2*q+8) (chirpLine s F)++S.R 146
    let S' : Stacks 263 A := {S with R := Function.update (Function.update (Function.update S.R 146 O) 110 X) 144 Y}
    ∃ v' n, v'.user = v.user ∧ n ≤ originalComponentInputsCost q s ∧
      Exec body familyOriginalComponentInputs (mk v S) n (mk v' S') ∧
      LengthKeyReady P N q l s t u band 0 0 X (embStk familyCouplingSourceReg S') := by
  dsimp only
  let T := embStk familyBoundaryReg S
  let X := cstream A (2*q+8) (chirpLine s (fun i => realPartWord (F i)))++tail
  let Y := cstream A (2*q+8) (chirpLine s (fun i => imagPartWord (F i)))++S.R 144
  let O := cstream A (2*q+8) (chirpLine s F)++S.R 146
  let S' : Stacks 263 A := {S with R := Function.update (Function.update (Function.update S.R 146 O) 110 X) 144 Y}
  obtain ⟨v₁,n,hu₁,hn,he,hready'⟩ := sharedPageOriginalComponentInputs_exec (body := fun p : Empty => nomatch p)
    hA F tail (embDn familyBoundaryReg v) T hready h147
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    familyBoundaryReg_injective (fun p => nomatch p) he v rfl S rfl
  have hproj : embStk familyBoundaryReg S' =
      {T with R := Function.update (Function.update (Function.update T.R 146 O) 110 X) 144 Y} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi146 : i = 146
    · subst i; rfl
    by_cases hi110 : i = 110
    · subst i; rfl
    by_cases hi144 : i = 144
    · subst i; rfl
    have h146 : familyBoundaryReg i ≠ 146 := familyBoundaryReg_injective.ne hi146
    have h110 : familyBoundaryReg i ≠ 110 := familyBoundaryReg_injective.ne hi110
    have h144 : familyBoundaryReg i ≠ 144 := familyBoundaryReg_injective.ne hi144
    simp only [S',T,embStk,Function.comp_def,Function.update_of_ne hi146,Function.update_of_ne hi110,
      Function.update_of_ne hi144,Function.update_of_ne h146,Function.update_of_ne h110,Function.update_of_ne h144]
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_,?_⟩
  · apply congrArg (mk v₂)
    let T₁ : Stacks 240 A := {T with R := Function.update T.R 146 O}
    let T₂ : Stacks 240 A := {T₁ with R := Function.update T₁.R 110 X}
    change embOvr familyBoundaryReg ({T₂ with R := Function.update T₂.R 144 Y} : Stacks 240 A).get S = S'
    rw [embOvr_updR familyBoundaryReg_injective]
    dsimp only [T₂]
    rw [embOvr_updR familyBoundaryReg_injective]
    dsimp only [T₁]
    rw [embOvr_updR familyBoundaryReg_injective,embOvr_stk]
    rfl
  · change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _
      (embStk componentReg (embStk boundaryComponentReg (embStk sharedPageRecoveryReg (embStk familyBoundaryReg S'))))
    rw [hproj]
    exact hready'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
