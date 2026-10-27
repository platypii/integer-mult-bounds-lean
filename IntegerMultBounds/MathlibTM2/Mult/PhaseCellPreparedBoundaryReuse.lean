module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundarySolve

/-! The prepared solve's output can remain published while the same factor bank accepts another RHS. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

theorem preparedBoundarySolve_project {A : ℕ} (S : Stacks 226 A) (output : List (Fin (A+4))) :
    embStk preparedBoundaryCoreReg
      {S with R := Function.update (Function.update S.R 206 []) 224 (output++S.R 224)} =
      {embStk preparedBoundaryCoreReg S with R := Function.update (embStk preparedBoundaryCoreReg S).R 206 []} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have h224 : preparedBoundaryCoreReg i ≠ 224 := (preparedBoundaryCoreReg_private i).1
  by_cases hi : i = 206
  · subst i
    simp [embStk,preparedBoundaryCoreReg]
  have h206 : preparedBoundaryCoreReg i ≠ 206 := preparedBoundaryCoreReg_injective.ne hi
  simp only [embStk,Function.comp_def,Function.update_of_ne h224,Function.update_of_ne h206,Function.update_of_ne hi]

theorem preparedBoundarySolve_factor_frame {A : ℕ} (S : Stacks 226 A) (output : List (Fin (A+4))) :
    boundaryFactorState (embStk preparedBoundaryCoreReg
      {S with R := Function.update (Function.update S.R 206 []) 224 (output++S.R 224)}) =
      Function.update (boundaryFactorState (embStk preparedBoundaryCoreReg S)) .vk [] := by
  rw [preparedBoundarySolve_project,boundaryFactorState_update_rhs]

theorem preparedBoundarySolve_ready {A q w W N : ℕ} (S : Stacks 226 A) (output : List (Fin (A+4)))
    (hready : BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg S)) q w W N) :
    BoundarySolveReady (boundaryFactorState (embStk preparedBoundaryCoreReg
      {S with R := Function.update (Function.update S.R 206 []) 224 (output++S.R 224)})) q w W N := by
  rw [preparedBoundarySolve_factor_frame]
  exact hready.update_vk []

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
