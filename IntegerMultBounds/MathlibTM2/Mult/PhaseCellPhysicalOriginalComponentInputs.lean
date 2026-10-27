module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginalComponentInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedResidualLift

/-! Preserve and split the original input in the full physical boundary bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 224 Q A U}

def boundaryComponentReg (i : Fin 148) : Fin 224 :=
  boundaryFactorLegacyReg (tableReg (boundaryArithmeticReg i))

theorem boundaryComponentReg_injective : Function.Injective boundaryComponentReg :=
  boundaryFactorLegacyReg_injective.comp (tableReg_injective.comp boundaryArithmeticReg_injective)

def physicalOriginalComponentInputs : Pr P₀ 224 Q A U :=
  embProg boundaryComponentReg Empty.elim (originalComponentInputs : Pr Empty 148 Q A U)

theorem physicalOriginalComponentInputs_exec {P N q l s t u band : ℕ} [NeZero s]
    (hA : 4 ≤ A) (F : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hready : LengthKeyReady P N q l s t u band 0 0
      (cstream A (2*q+8) (chirpLine s F)++tail) (embStk componentReg (embStk boundaryComponentReg S)))
    (h147 : S.R 147 = []) :
    let X := cstream A (2*q+8) (chirpLine s (fun i => realPartWord (F i)))++tail
    let Y := cstream A (2*q+8) (chirpLine s (fun i => imagPartWord (F i)))++S.R 144
    let O := cstream A (2*q+8) (chirpLine s F)++S.R 146
    let S' : Stacks 224 A := {S with R := Function.update (Function.update (Function.update S.R 146 O) 110 X) 144 Y}
    ∃ v' n, v'.user = v.user ∧ n ≤ originalComponentInputsCost q s ∧
      Exec body physicalOriginalComponentInputs (mk v S) n (mk v' S') ∧
      LengthKeyReady P N q l s t u band 0 0 X (embStk componentReg (embStk boundaryComponentReg S')) := by
  dsimp only
  let e := boundaryComponentReg
  let X := cstream A (2*q+8) (chirpLine s (fun i => realPartWord (F i)))++tail
  let Y := cstream A (2*q+8) (chirpLine s (fun i => imagPartWord (F i)))++S.R 144
  let O := cstream A (2*q+8) (chirpLine s F)++S.R 146
  let S' : Stacks 224 A := {S with R := Function.update (Function.update (Function.update S.R 146 O) 110 X) 144 Y}
  obtain ⟨v₁,n,hu,hn,he,hready'⟩ := originalComponentInputs_exec (body := Empty.elim)
    hA F tail (embDn e v) (embStk e S) hready h147
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body) boundaryComponentReg_injective
    (fun p : Empty => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu,hn,he₂.cast rfl ?_,?_⟩
  · apply congrArg (mk v₂)
    let S₁ : Stacks 148 A := {embStk e S with R := Function.update (embStk e S).R 146 O}
    let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 110 X}
    change embOvr e ({S₂ with R := Function.update S₂.R 144 Y} : Stacks 148 A).get S = S'
    rw [embOvr_updR boundaryComponentReg_injective]
    dsimp only [S₂]
    rw [embOvr_updR boundaryComponentReg_injective]
    dsimp only [S₁]
    rw [embOvr_updR boundaryComponentReg_injective,embOvr_stk]
    rfl
  · have hproject : embStk e S' = {embStk e S with R :=
        (Function.update (Function.update (Function.update (embStk e S).R 146 O) 110 X) 144 Y)} := by
      let T₁ : Stacks 224 A := {S with R := Function.update S.R 146 O}
      let T₂ : Stacks 224 A := {T₁ with R := Function.update T₁.R 110 X}
      have hT₁ : embStk e T₁ = {embStk e S with R := Function.update (embStk e S).R 146 O} :=
        embStk_updateR_inner e boundaryComponentReg_injective S 146 O
      have hT₂ : embStk e T₂ = {embStk e T₁ with R := Function.update (embStk e T₁).R 110 X} :=
        embStk_updateR_inner e boundaryComponentReg_injective T₁ 110 X
      have hT₃ : embStk e S' = {embStk e T₂ with R := Function.update (embStk e T₂).R 144 Y} :=
        embStk_updateR_inner e boundaryComponentReg_injective T₂ 144 Y
      rw [hT₃,hT₂,hT₁]
    change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _ (embStk componentReg (embStk e S'))
    rw [hproject]
    exact hready'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
