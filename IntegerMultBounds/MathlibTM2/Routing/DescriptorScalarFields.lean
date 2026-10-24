module

public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorScalarPalette

/-! The shared scalar palette installs precisely the five scalar roles of each
repair descriptor. This identifies the generated words with the caller contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section

def descriptorScalarRole (j : Fin 11) : Fin 5 → LiveDescriptorRole 11 :=
  ![.stride j, .base j, .last j, .rows j, .sourceWidth j]

theorem descriptorScalarRole_injective :
    Function.Injective (fun q : Fin 11 × Fin 5 => descriptorScalarRole q.1 q.2) := by
  rintro ⟨j, f⟩ ⟨k, g⟩ h
  fin_cases f <;> fin_cases g <;> simp_all [descriptorScalarRole]

theorem descriptorScalarRole_operands {A : ℕ} (p : Par) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (source : Fin p.n → SlotSource p 0)
    (w : LiveDescriptorWidths) (j : Fin 11) (field : Fin 5) :
    (binSyms (repairDescriptorScalarWidth w field)
      (repairDescriptorScalarPalette p (repairDescriptorScalarSlot j field)) : List (Fin (A + 4))) =
      canonicalDescriptorOperands p 0 hG hK active source w (descriptorScalarRole j field) := by
  rw [repairDescriptorScalarPalette_words]
  fin_cases field <;>
    simp [descriptorScalarRole, repairDescriptorScalarWidth, repairDescriptorScalarValues,
      canonicalDescriptorOperands, liveDescriptorData]

end
end IntegerMultBounds.MathlibTM2.Routing
