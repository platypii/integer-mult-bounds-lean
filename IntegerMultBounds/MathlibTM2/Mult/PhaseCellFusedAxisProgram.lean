module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerRawProgram
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoopSharedStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedClassInput

/-! Outer S4 control separates R4 movement from the numerical core. Calling the
complete raw caller on every axis would also call sharedGatherProgram on every
axis, repaying its exposure. Instead R4 routes an already exposed tensor into
the computed class bank and returns numerical results through its own layout.

The program is fixed: axis count, dimensions and packet widths are tape data.
Publication reuses the verified full continuation, including ordinary control
producers. Preparation/routing/tensor-return suppliers still need an outer
execution proof. This construction alone is not an outer execution theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement ScalarPlacement.ComputedClassBanks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ} {P U : Type}
noncomputable section

/-- Reuse setup, numerical execution, full publication and retirement verbatim.
R4 supplies only the input movement context; shared exposure stays outside it. -/
def fusedProperProgram (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q)
    (routeProper : Pr P (MachineTapes T) Q (prime+K) U →
      Pr P (MachineTapes T) Q (prime+K) U) : Pr P (MachineTapes T) Q (prime+K) U :=
  let physicalBank := CallerLayout.bank bank
  let physicalInj := bank_injective bank hinj
  let numerical := inputTableClassProgram (numericTable T) (masterSources T) (globals T 0) (fullHeader T .zero)
    (initializedClassProgram (fullExposedClassBank physicalBank) (geometrySources T)
      (routeProper (inputClassProgram (fullExposedClassBank physicalBank)
        (fullExposedClassBank_injective physicalBank physicalInj) b (numericTable T))))
  .seq (sharedClassSetupProgram T)
    (.seq (publishedClassProgram numerical (routing T) (publication T)
      (physicalBank (.recovery (.control .result))) (header T .output) hstates)
      (sharedClassRetireProgram T))

/-- The verified proper caller is precisely the old input-movement instance.
The fused construction changes no publication or numerical code. -/
theorem sharedProperProgram_eq_fusedProperProgram
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q) :
    sharedProperProgram (P := P) bank hinj b hstates =
      fusedProperProgram bank hinj b hstates (fun numerical => .seq (sharedGatherProgram bank hstates) numerical) := by
  rfl

/-- Prepare one axis from the shared tensor, execute the proper class and seam
fallback, retire owned controls, then restore the tensor layout for the next axis.
Publication reuses the complete verified caller continuation, including control
generation and retirement. The alternative export branch is in commit 19b8e368. -/
def fusedAxisStep (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (widths : Fin 3 → Fin T) (recovery : Bool)
    (routeCount routeOutput routeSaved routeTmp : Fin (MachineTapes (T+solverRegisterCount)))
    (hstates : FixedStreamedBank.stateCount ≤ Q)
    (prepareAxis routeProper returnAxis :
      Pr P (MachineTapes (T+solverRegisterCount)) Q (prime+K) U) :
    Pr P (MachineTapes (T+solverRegisterCount)) Q (prime+K) U :=
  .seq prepareAxis
    (.seq (.seq (callerCanonicalInputPreparation src)
      (gatherPreparationProgram (solverSource ∘ src) (solverSource widthSource) (solverSource ∘ widths)))
      (.seq (fusedProperProgram (solverSource ∘ bank) ((Fin.castAdd_injective _ _).comp hinj)
        b hstates (fun numerical => .seq routeProper (.seq (installRoutedClassInput
          (fullExposedClassBank (CallerLayout.bank (solverSource ∘ bank)))
          routeCount routeOutput routeSaved routeTmp) numerical)))
        (.seq (callerBoundaryCompletion src b.hR b.hQ (solverSource widthSource) recovery)
          (.seq (clearWords (sharedBoundaryHeaders T)) returnAxis))))

/-- One runtime counted loop, rather than a program unrolled over axis metadata.
The existing counted-loop shared-stock theorem supplies the outer composition
once the concrete stage invariant and R4 suppliers are discharged. -/
def fusedAxesProgram (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (widths : Fin 3 → Fin T) (recovery : Bool)
    (routeCount routeOutput routeSaved routeTmp : Fin (MachineTapes (T+solverRegisterCount)))
    (hstates : FixedStreamedBank.stateCount ≤ Q)
    (count : Fin (MachineTapes (T+solverRegisterCount)))
    (prepareAxis routeProper returnAxis :
      Pr P (MachineTapes (T+solverRegisterCount)) Q (prime+K) U) :
    Pr P (MachineTapes (T+solverRegisterCount)) Q (prime+K) U :=
  countedLoop count (fusedAxisStep bank hinj b src widthSource widths recovery
    routeCount routeOutput routeSaved routeTmp
    hstates prepareAxis routeProper returnAxis)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
