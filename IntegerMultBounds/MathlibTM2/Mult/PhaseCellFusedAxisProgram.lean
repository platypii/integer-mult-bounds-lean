module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerRawProgram
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoopSharedStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedClassInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoutedPublicationProgram

/-! Outer S4 control separates R4 movement from the numerical core. Calling the
complete raw caller on every axis would also call sharedGatherProgram on every
axis, repaying its exposure. Instead R4 routes an already exposed tensor into
the computed class bank and returns numerical results through its own layout.

The program is fixed: axis count, dimensions and packet widths are tape data.
Publication has a concrete placed program. Its ordinary readiness, and the
preparation/routing/tensor-return suppliers, still need an outer execution
proof. This construction alone is not an outer execution theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement ScalarPlacement.ComputedClassBanks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ} {P U : Type}
noncomputable section

/-- Retain the executed numerical/setup/retirement code, with R4 supplying both
movement directions. In particular this program does not invoke sharedGatherProgram. -/
def fusedProperProgram (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U)
    (routeProper : Pr P (MachineTapes T) Q (prime+K) U →
      Pr P (MachineTapes T) Q (prime+K) U)
    (publishProper : Pr P (MachineTapes T) Q (prime+K) U →
      Pr P (MachineTapes T) Q (prime+K) U) :
    Pr P (MachineTapes T) Q (prime+K) U :=
  let physicalBank := CallerLayout.bank bank
  let physicalInj := bank_injective bank hinj
  let numerical := inputTableClassProgram (numericTable T) (masterSources T) (globals T 0) (fullHeader T .zero)
    (initializedClassProgram (fullExposedClassBank physicalBank) (geometrySources T)
      (routeProper (inputClassProgram (fullExposedClassBank physicalBank)
        (fullExposedClassBank_injective physicalBank physicalInj) b (numericTable T))))
  .seq (sharedClassSetupProgram T)
    (.seq (publishProper numerical) (sharedClassRetireProgram T))

/-- The verified single-axis proper program is an instance of this same
numerical construction. R4 replaces the movement contexts, not the solver. -/
theorem sharedProperProgram_eq_fusedProperProgram
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q) :
    sharedProperProgram (P := P) bank hinj b hstates =
      fusedProperProgram bank hinj b (fun numerical => .seq (sharedGatherProgram bank hstates) numerical)
        (fun numerical => publishedClassProgram numerical (routing T) (publication T)
          ((CallerLayout.bank bank) (.recovery (.control .result))) (header T .output) hstates) := by
  rfl

/-- Reuse the routing suffix, sharing exactly the numerical result and output
header with the caller. Other caller storage is outside the private bank. -/
def fusedPublicationPlacement (bank : ComputedClassBank → Fin T) :
    Fin PackedTranspose.tapeCount → Fin (MachineTapes T) :=
  PackedTranspose.publicationPlacement
    (Fin.castAdd 175 ((CallerLayout.bank bank) (.recovery (.control .result))))
    (Fin.castAdd 175 (header T .output))

theorem fusedPublicationPlacement_injective (bank : ComputedClassBank → Fin T) :
    Function.Injective (fusedPublicationPlacement bank) := by
  apply PackedTranspose.publicationPlacement_injective
  exact (Fin.castAdd_injective _ _).ne (header_ne_bank bank .output (.recovery (.control .result))).symm

theorem fusedPublicationPlacement_numerical (bank : ComputedClassBank → Fin T) :
    fusedPublicationPlacement bank PackedTranspose.numericalPort =
      fullExposedClassBank (CallerLayout.bank bank) (.recovery (.control .result)) := by
  rw [fusedPublicationPlacement,PackedTranspose.publicationPlacement_numerical,fullExposedClassBank_apply]
  simp only [classCallerRegister,exposureIntoRouting]

theorem fusedPublicationPlacement_ambient (bank : ComputedClassBank → Fin T) :
    fusedPublicationPlacement bank PackedTranspose.ambientPort = fullHeader T .output := by
  rw [fusedPublicationPlacement,PackedTranspose.publicationPlacement_ambient]
  simp only [fullHeader,classCallerRegister,exposureIntoRouting]

def fusedPublicationProgram (bank : ComputedClassBank → Fin T)
    (hstates : FixedStreamedBank.stateCount ≤ Q) : Pr P (MachineTapes T) Q (prime+K) U :=
  embProg (fusedPublicationPlacement bank) Empty.elim
    (PackedTranspose.standardRoutedPublicationProgram (P := Empty) hstates)

/-- Prepare one axis from the shared tensor, execute the proper class and seam
fallback, retire owned controls, then restore the tensor layout for the next axis.
Publication uses the checked standard bank, including its consuming export. -/
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
        b (fun numerical => .seq routeProper (.seq (installRoutedClassInput
          (fullExposedClassBank (CallerLayout.bank (solverSource ∘ bank)))
          routeCount routeOutput routeSaved routeTmp) numerical))
        (fun numerical => .seq numerical (fusedPublicationProgram (solverSource ∘ bank) hstates)))
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
