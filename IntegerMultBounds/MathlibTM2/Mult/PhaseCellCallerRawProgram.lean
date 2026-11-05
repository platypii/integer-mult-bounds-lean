module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerFixedProgram
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerBoundaryCompletion
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSharedBoundaryRetirement

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ} {P U : Type}
noncomputable section

/-- One raw S4 caller program. All dimensions, precision, replica counts and
numerical inputs are read from tapes; no prepared state or mathematical witness
is an argument of the program. -/
def rawBoundaryProgram (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (widths : Fin 3 → Fin T) (recovery : Bool) :
    Pr P (MachineTapes (T+solverRegisterCount)) Q (prime+K) U :=
  let proper := sharedProperProgram (solverSource ∘ bank) ((Fin.castAdd_injective _ _).comp hinj) b hstates
  .seq (.seq (callerCanonicalInputPreparation src)
    (gatherPreparationProgram (solverSource ∘ src) (solverSource widthSource) (solverSource ∘ widths)))
    (.seq (.seq proper (callerBoundaryCompletion src b.hR b.hQ (solverSource widthSource) recovery))
      (clearWords (sharedBoundaryHeaders T)))

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
