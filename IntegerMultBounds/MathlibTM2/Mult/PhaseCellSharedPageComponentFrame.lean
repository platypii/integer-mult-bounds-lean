module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryReady

/-! Component switching preserves prepared factors and changes only the logical arithmetic source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

private theorem project_transition {A : ℕ} (S : Stacks 240 A)
    (input parked saved : List (Fin (A+4))) :
    embStk sharedPageRecoveryReg {S with R := (Function.update (Function.update (Function.update S.R
      110 input) 144 parked) 145 saved)} =
      {embStk sharedPageRecoveryReg S with R := (Function.update (Function.update (Function.update
        (embStk sharedPageRecoveryReg S).R 110 input) 144 parked) 145 saved)} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi110 : i = 110
  · subst i; rfl
  by_cases hi144 : i = 144
  · subst i; rfl
  by_cases hi145 : i = 145
  · subst i; rfl
  have h110 : sharedPageRecoveryReg i ≠ 110 := sharedPageRecoveryReg_injective.ne hi110
  have h144 : sharedPageRecoveryReg i ≠ 144 := sharedPageRecoveryReg_injective.ne hi144
  have h145 : sharedPageRecoveryReg i ≠ 145 := sharedPageRecoveryReg_injective.ne hi145
  simp only [embStk,Function.comp_def,Function.update_of_ne hi110,Function.update_of_ne hi144,
    Function.update_of_ne hi145,Function.update_of_ne h110,Function.update_of_ne h144,Function.update_of_ne h145]

theorem sharedPageArithmetic_transition {A : ℕ} (S : Stacks 240 A)
    (input parked saved : List (Fin (A+4))) :
    embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg
      (embStk sharedPageRecoveryReg {S with R := (Function.update (Function.update (Function.update S.R
        110 input) 144 parked) 145 saved)})))) =
      {embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg
        (embStk sharedPageRecoveryReg S)))) with R := (Function.update
          (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg
            (embStk sharedPageRecoveryReg S))))).R 110 input)} := by
  rw [project_transition,boundaryRecoveryProject_transition]

theorem sharedPageFactor_transition {A : ℕ} (S : Stacks 240 A)
    (input parked saved : List (Fin (A+4))) :
    boundaryFactorState (embStk sharedPageRecoveryReg {S with R := (Function.update
      (Function.update (Function.update S.R 110 input) 144 parked) 145 saved)}) =
      boundaryFactorState (embStk sharedPageRecoveryReg S) := by
  funext r
  cases r <;> first | rfl | (rename_i c; cases c <;> rfl)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
