module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryGatherSolve

/-! The triangular solver changes exactly its RHS and solution ports; all prepared pages survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

theorem boundarySolve_frame_exact {A : ℕ} (S S' : Stacks 224 A) (output : List (Fin (A+4)))
    (hframe : RsbFr boundaryFactorReg S S')
    (hlegacy : ∀ i : Fin 154, S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i))
    (hpost : boundaryFactorState S' = Function.update (Function.update (boundaryFactorState S) .vk []) .dout output) :
    S' = {S with R := Function.update (Function.update S.R 206 []) 217 output} := by
  refine Stacks.ext hframe.1 hframe.2.1 hframe.2.2.1 ?_
  funext i
  change S'.R i = Function.update (Function.update S.R 206 []) 217 output i
  by_cases hi217 : i = 217
  · subst i
    exact congrFun hpost .dout
  by_cases hi206 : i = 206
  · subst i
    exact congrFun hpost .vk
  simp only [Function.update_of_ne hi217,Function.update_of_ne hi206]
  by_cases hi : i.val < 154
  · let j : Fin 154 := ⟨i.val,hi⟩
    have hj : boundaryFactorLegacyReg j = i := Fin.ext rfl
    rw [← hj]
    exact hlegacy j
  by_cases hi184 : i = 184
  · subst i
    exact hframe.2.2.2 184 (fun r => (boundaryFactorReg_private r).1)
  by_cases hi223 : i = 223
  · subst i
    exact hframe.2.2.2 223 (fun r => (boundaryFactorReg_private r).2)
  obtain ⟨r,hr⟩ := boundaryFactorReg_cover i (by omega) hi184 hi223
  have hrvk : r ≠ .vk := by intro he; subst r; exact hi206 hr.symm
  have hrdout : r ≠ .dout := by intro he; subst r; exact hi217 hr.symm
  have hh := congrFun hpost r
  simp only [Function.update_of_ne hrvk,Function.update_of_ne hrdout] at hh
  change S'.R (boundaryFactorReg r) = S.R (boundaryFactorReg r) at hh
  simpa only [hr] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
