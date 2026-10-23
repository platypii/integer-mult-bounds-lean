module

public import IntegerMultBounds.MathlibTM2.Routing.EmbeddedRepairWidths
public import IntegerMultBounds.MathlibTM2.Routing.InactiveProfileHeaderRepair

/-! Width generation around the header/inactive-profile bank preserves all
profile, count and header inputs. The two generated raw fields start blank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev inactiveProfileConfigurationT := inactiveProfileHeaderT + 6

theorem inactiveProfileHeaderRaw_injective : Function.Injective inactiveProfileHeaderRaw :=
  embeddedRepairHeaderRaw_injective inactiveProfileRaw inactiveProfileRaw_injective

def inactiveProfileWidthBank {A : ℕ} (rb wy : ℕ)
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) :=
  embeddedRepairWidthBank inactiveProfileHeaderRaw rb wy bank

variable {A : ℕ}

theorem inactiveProfileWidthBank_raw (rb wy : ℕ)
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (i : Fin repairT)
    (hr : i ≠ repairSetupSource (.inr .row)) (hm : i ≠ repairSetupSource (.inr .keyMask)) :
    inactiveProfileWidthBank rb wy bank (fieldCore (inactiveProfileHeaderRaw i)) =
      bank (fieldCore (inactiveProfileHeaderRaw i)) :=
  embeddedRepairWidthBank_raw inactiveProfileHeaderRaw inactiveProfileHeaderRaw_injective rb wy bank i hr hm

theorem inactiveProfileWidthBank_liveAux (rb wy : ℕ)
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (r : LiveDescriptorRole 11) :
    inactiveProfileWidthBank rb wy bank
      (fieldCore (sharedHeaderCore (liveInactiveProfileCore (liveDescriptorAux r)))) =
      bank (fieldCore (sharedHeaderCore (liveInactiveProfileCore (liveDescriptorAux r)))) := by
  apply embeddedRepairWidthBank_keep
  · exact sharedHeaderCore_injective.ne (liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux _ r).symm)
  · exact sharedHeaderCore_injective.ne (liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux _ r).symm)

theorem inactiveProfileWidthBank_profileAux (rb wy : ℕ)
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (i : Fin 7) :
    inactiveProfileWidthBank rb wy bank (fieldCore (sharedHeaderCore (liveInactiveProfileAux i))) =
      bank (fieldCore (sharedHeaderCore (liveInactiveProfileAux i))) := by
  apply embeddedRepairWidthBank_keep
  · exact sharedHeaderCore_injective.ne (liveInactiveProfileAux_core _ _)
  · exact sharedHeaderCore_injective.ne (liveInactiveProfileAux_core _ _)

theorem inactiveProfileWidthBank_headerWork (rb wy : ℕ)
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (r : HeaderWorkRole) :
    inactiveProfileWidthBank rb wy bank (fieldCore (sharedHeaderWork r)) =
      bank (fieldCore (sharedHeaderWork r)) := by
  apply embeddedRepairWidthBank_keep
  · exact (sharedHeaderCore_work _ r).symm
  · exact (sharedHeaderCore_work _ r).symm

theorem RepairPendingConfigurationData.inactiveProfileWidths (p : Par) (X rb : ℕ)
    {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))}
    (data : RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => bank (fieldCore (inactiveProfileHeaderRaw i)))) :
    RepairPendingDescriptorData p X rb wb wm wp wk R B headers
      (fun i => inactiveProfileWidthBank rb p.wy bank (fieldCore (inactiveProfileHeaderRaw i))) :=
  data.embeddedWidths inactiveProfileHeaderRaw inactiveProfileHeaderRaw_injective p X rb

end
end IntegerMultBounds.MathlibTM2.Routing
