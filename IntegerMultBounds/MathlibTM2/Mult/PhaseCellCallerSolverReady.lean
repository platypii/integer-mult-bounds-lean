module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolverAllocation

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast CommonClassGeometry ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T A s : ℕ} [NeZero s]
noncomputable section

/-- The eight inverse parameters come directly from retained caller rulers. -/
theorem solverParameter_lengths (src : Fin 11 → Fin T)
    (p u l target t B W N radius width : ℕ)
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hraw : ∀ i, (S.R (unarySource _ (solverSource (src i)))).length =
      globalValues p u l target s t B W N radius width i)
    (hzero : S.R (fullHeader _ .zero) = []) :
    ∀ i, (S.R (solverParameter T src i)).length = ![p,u,l,target,s,t,0,s] i := by
  intro i
  change (S.R (solverParameter T src i)).length = _
  fin_cases i
  · simpa [solverParameter,solverParameterSource,globalValues] using hraw 0
  · simpa [solverParameter,solverParameterSource,globalValues] using hraw 1
  · simpa [solverParameter,solverParameterSource,globalValues] using hraw 2
  · simpa [solverParameter,solverParameterSource,globalValues] using hraw 3
  · simpa [solverParameter,solverParameterSource,globalValues] using hraw 4
  · simpa [solverParameter,solverParameterSource,globalValues] using hraw 5
  · simp [solverParameter,solverParameterSource,hzero]
  · simpa [solverParameter,solverParameterSource,globalValues] using hraw 4

/-- Ordinary caller rulers, a borrowed width word and fresh solver storage
discharge the concrete full-line input contract. -/
theorem callerFullLineInput_ready (src : Fin 11 → Fin T)
    (p u l target t B W radius width : ℕ) (Fs : List (ZMod s → GaussianInt))
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hraw : ∀ i, (S.R (unarySource _ (solverSource (src i)))).length =
      globalValues p u l target s t B W Fs.length radius width i)
    (hzero : S.R (fullHeader _ .zero) = [])
    (hwidth : S.R (solverRegister T (.input (familyInverseScalarReg .wr))) =
      List.replicate (inverseCallerWordWidth p u l target s t) tick)
    (hblank : ∀ i, i ≠ familyInverseScalarReg .wr → S.R (solverRegister T (.input i)) = [])
    (hleft : ∀ i, S.L (solverRegister T (.input i)) = [])
    (hscratch : ∀ i : Fin 4, S.R (solverRegister T (.scratch (Fin.castAdd 1 i))) = [])
    (hambient : S.R (solverRegister T (.scratch 4)) =
      cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten) :
    (callerFullLineInput T src).Ready p u l target t Fs S := by
  refine ⟨?_,hwidth,hblank,hleft,?_,hambient,?_⟩
  · exact solverParameter_lengths src p u l target t B W Fs.length radius width S hraw hzero
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact hscratch 0
    · exact hscratch 1
    · exact hscratch 2
    · exact hscratch 3
  · change (S.R (unarySource _ (solverSource (src 8)))).length = Fs.length
    simpa [globalValues] using hraw 8

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
