module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposedClassGeometryFrame

/-! The publication allocation reuses exactly the selected caller's routing
suffix, numerical result register and ambient caller destination. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host PackedTranspose
variable {T : ℕ}
noncomputable section

def selectedPublicationPlacement (bank : ComputedClassBank → Fin T) (output : Fin T) :
    Fin PackedTranspose.tapeCount → Fin ((T+175)+PackedTranspose.tapeCount) :=
  publicationPlacement (Fin.castAdd 175 (bank (.recovery (.control .result)))) (Fin.castAdd 175 output)

theorem selectedPublicationPlacement_injective (bank : ComputedClassBank → Fin T) (output : Fin T)
    (hout : bank (.recovery (.control .result)) ≠ output) :
    Function.Injective (selectedPublicationPlacement bank output) :=
  publicationPlacement_injective _ _ ((Fin.castAdd_injective T 175).ne hout)

theorem selectedPublicationPlacement_numerical (bank : ComputedClassBank → Fin T)
    (hinj : Function.Injective bank) (output : Fin T) :
    selectedPublicationPlacement bank output numericalPort =
      (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).result := by
  simp only [selectedPublicationPlacement,publicationPlacement_numerical,plan,RecoveryBanks.plan,
    recovery,fullExposedClassBank_apply,classCallerRegister,exposureIntoRouting]

theorem selectedPublicationPlacement_ambient (bank : ComputedClassBank → Fin T) (output : Fin T) :
    selectedPublicationPlacement bank output ambientPort = classCallerRegister output := by
  simp only [selectedPublicationPlacement,publicationPlacement_ambient,classCallerRegister,exposureIntoRouting]

theorem selectedPublicationPlacement_private (bank : ComputedClassBank → Fin T) (output : Fin T)
    (i : Fin PackedTranspose.tapeCount) (hnum : i ≠ numericalPort) (hout : i ≠ ambientPort) :
    selectedPublicationPlacement bank output i = Fin.natAdd (T+175) i :=
  publicationPlacement_private _ _ i hnum hout

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
