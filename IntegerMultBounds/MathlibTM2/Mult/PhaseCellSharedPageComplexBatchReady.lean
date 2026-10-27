module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageComplexBatchStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryReady

/-! Advancing a replica changes only the arithmetic input in the retained page views. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def sharedComplexBatchNext {A : ℕ} (S : Stacks 248 A)
    (input output tail : List (Fin (A+4))) : Stacks 248 A :=
  {S with R := (Function.update (Function.update (Function.update S.R
    110 tail) 241 (input.reverse++S.R 241)) 242 (output.reverse++S.R 242))}

theorem sharedComplexBatchNext_core {A : ℕ} (S : Stacks 248 A)
    (input output tail : List (Fin (A+4))) :
    embStk sharedComplexBatchCoreReg (sharedComplexBatchNext S input output tail) =
      {(embStk sharedComplexBatchCoreReg S) with R :=
        (Function.update (embStk sharedComplexBatchCoreReg S).R 110 tail)} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = 110
  · subst i; rfl
  have hn : sharedComplexBatchCoreReg i ≠ 110 := sharedComplexBatchCoreReg_injective.ne hi
  simp only [sharedComplexBatchNext,embStk,Function.comp_def,
    Function.update_of_ne (sharedComplexBatchCoreReg_off i 242 (by decide)),
    Function.update_of_ne (sharedComplexBatchCoreReg_off i 241 (by decide)),
    Function.update_of_ne hn,Function.update_of_ne hi]

theorem sharedComplexBatchNext_ready {A P N q l s t u band V w : ℕ}
    (S : Stacks 248 A) (input output tail source : List (Fin (A+4)))
    (hready : LengthKeyReady P N q l s t u band V w source
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg (embStk sharedComplexBatchCoreReg S))))))) :
    LengthKeyReady P N q l s t u band V w tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
        (embStk boundaryFactorLegacyReg (embStk sharedPageRecoveryReg
          (embStk sharedComplexBatchCoreReg (sharedComplexBatchNext S input output tail))))))) := by
  rw [sharedComplexBatchNext_core]
  have hproject : embStk sharedPageRecoveryReg
      ({(embStk sharedComplexBatchCoreReg S) with R :=
        (Function.update (embStk sharedComplexBatchCoreReg S).R 110 tail)} : Stacks 240 A) =
      {(embStk sharedPageRecoveryReg (embStk sharedComplexBatchCoreReg S)) with R :=
        (Function.update (embStk sharedPageRecoveryReg (embStk sharedComplexBatchCoreReg S)).R 110 tail)} :=
    embStk_updateR_inner sharedPageRecoveryReg sharedPageRecoveryReg_injective
      (embStk sharedComplexBatchCoreReg S) 110 tail
  rw [hproject]
  have hr := boundaryRecoveryReady_of_frame hready (S' :=
    {(embStk sharedPageRecoveryReg (embStk sharedComplexBatchCoreReg S)) with R :=
      (Function.update (embStk sharedPageRecoveryReg (embStk sharedComplexBatchCoreReg S)).R 110 tail)})
    rfl rfl rfl (by
      intro i h109 h110 h115 h116 h132
      have hn : boundaryFactorLegacyReg i ≠ 110 := boundaryFactorLegacyReg_injective.ne h110
      exact Function.update_of_ne hn _ _)
  simpa only [Function.update_self] using hr

theorem sharedComplexBatchNext_factor {A : ℕ} (S : Stacks 248 A)
    (input output tail : List (Fin (A+4))) :
    boundaryFactorState (embStk sharedPageRecoveryReg
      (embStk sharedComplexBatchCoreReg (sharedComplexBatchNext S input output tail))) =
      boundaryFactorState (embStk sharedPageRecoveryReg (embStk sharedComplexBatchCoreReg S)) := by
  rw [sharedComplexBatchNext_core]
  funext r
  cases r <;> first | rfl | (rename_i c; cases c <;> rfl)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
