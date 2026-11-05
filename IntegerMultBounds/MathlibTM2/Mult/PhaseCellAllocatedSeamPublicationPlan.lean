module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationHeaderPlacement

/-! Place the restoring seam plan in the existing fixed routing bank, sharing
only the source archive and ambient destination with the caller prefix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
noncomputable section
variable {T : ℕ}

def seamRegister (src dst : Fin T) (i : Fin 117) : Fin (T+tapeCount) :=
  publicationPlacement src dst (publicationReg i)

theorem seamRegister_injective (src dst : Fin T) (hne : src ≠ dst) :
    Function.Injective (seamRegister src dst) :=
  (publicationPlacement_injective src dst hne).comp publicationReg_injective

@[simp] theorem seamRegister_source (src dst : Fin T) :
    seamRegister src dst 95 = Fin.castAdd tapeCount src :=
  publicationPlacement_numerical src dst

@[simp] theorem seamRegister_destination (src dst : Fin T) :
    seamRegister src dst 96 = Fin.castAdd tapeCount dst :=
  publicationPlacement_ambient src dst

theorem seamRegister_private (src dst : Fin T) (i : Fin 117) (hsrc : i ≠ 95) (hdst : i ≠ 96) :
    seamRegister src dst i = Fin.natAdd T (publicationReg i) :=
  publicationPlacement_private src dst _ (publicationReg_injective.ne hsrc) (publicationReg_injective.ne hdst)

def allocatedSeamPublicationPlan (src dst : Fin T) (hne : src ≠ dst) :
    PreparedPublicationPlan (T+tapeCount) (Fin.castAdd tapeCount src) (Fin.castAdd tapeCount dst) := by
  simpa only [seamRegister_source,seamRegister_destination] using
    standardSeamPublicationPlan.map (seamRegister src dst) (seamRegister_injective src dst hne)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
