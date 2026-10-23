module

public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierPair
public import IntegerMultBounds.MathlibTM2.Routing.InactiveWidthRepair
public import IntegerMultBounds.MathlibTM2.Routing.InactiveProfileWidths

/-! Generated classifiers preserve every other exact-repair input: descriptors,
widths, scratch, installation destinations and the original record stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

def inactiveConfigurationCore (i : Fin repairT) : Fin inactiveProfileConfigurationT :=
  fieldCore (inactiveProfileHeaderRaw i)

theorem inactiveConfigurationCore_injective : Function.Injective inactiveConfigurationCore :=
  fieldCore_injective.comp inactiveProfileHeaderRaw_injective

theorem inactiveConfigurationSource_src (key : RepairSetupKey) :
    inactiveConfigurationCore (repairSetupSource key) ≠ inactiveConfigurationCore repairHost.src :=
  inactiveConfigurationCore_injective.ne (repairSetup_source_src key)

variable {A : ℕ} (p : Par)

def inactiveConfigurationClassifierBank (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) :=
  repairClassifierGenerated p inactiveConfigurationCore bank

theorem inactiveConfigurationClassifierBank_keep
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (i : Fin inactiveProfileConfigurationT)
    (ht : i ≠ inactiveConfigurationCore (repairSetupSource (.inr .badMask)))
    (hp : i ≠ inactiveConfigurationCore (repairSetupSource (.inr .badPhase))) :
    inactiveConfigurationClassifierBank p bank i = bank i := by
  simp [inactiveConfigurationClassifierBank, repairClassifierGenerated, ht, hp]

theorem inactiveConfigurationClassifierBank_core
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (i : Fin repairT)
    (ht : i ≠ repairSetupSource (.inr .badMask)) (hp : i ≠ repairSetupSource (.inr .badPhase)) :
    inactiveConfigurationClassifierBank p bank (inactiveConfigurationCore i) = bank (inactiveConfigurationCore i) :=
  inactiveConfigurationClassifierBank_keep p bank _ (inactiveConfigurationCore_injective.ne ht)
    (inactiveConfigurationCore_injective.ne hp)

theorem inactiveConfigurationClassifierBank_widthAux
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (i : Fin 6) :
    inactiveConfigurationClassifierBank p bank (fieldAux i) = bank (fieldAux i) :=
  inactiveConfigurationClassifierBank_keep p bank _ (fieldCore_aux _ i).symm (fieldCore_aux _ i).symm

theorem inactiveConfigurationClassifierBank_liveAux
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (r : LiveDescriptorRole 11) :
    inactiveConfigurationClassifierBank p bank (fieldCore (sharedHeaderCore (liveInactiveProfileCore (liveDescriptorAux r)))) =
      bank (fieldCore (sharedHeaderCore (liveInactiveProfileCore (liveDescriptorAux r)))) := by
  apply inactiveConfigurationClassifierBank_keep
  · exact fieldCore_injective.ne (sharedHeaderCore_injective.ne (liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux _ r).symm))
  · exact fieldCore_injective.ne (sharedHeaderCore_injective.ne (liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux _ r).symm))

theorem inactiveConfigurationClassifierBank_profileAux
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (i : Fin 7) :
    inactiveConfigurationClassifierBank p bank (fieldCore (sharedHeaderCore (liveInactiveProfileAux i))) =
      bank (fieldCore (sharedHeaderCore (liveInactiveProfileAux i))) := by
  apply inactiveConfigurationClassifierBank_keep
  · exact fieldCore_injective.ne (sharedHeaderCore_injective.ne (liveInactiveProfileAux_core _ _))
  · exact fieldCore_injective.ne (sharedHeaderCore_injective.ne (liveInactiveProfileAux_core _ _))

theorem inactiveConfigurationClassifierBank_headerWork
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (r : HeaderWorkRole) :
    inactiveConfigurationClassifierBank p bank (fieldCore (sharedHeaderWork r)) =
      bank (fieldCore (sharedHeaderWork r)) := by
  apply inactiveConfigurationClassifierBank_keep
  · exact fieldCore_injective.ne (sharedHeaderCore_work _ r).symm
  · exact fieldCore_injective.ne (sharedHeaderCore_work _ r).symm

theorem inactiveConfigurationClassifierBank_targets
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (key : RepairSetupKey) :
    inactiveConfigurationClassifierBank p bank (inactiveConfigurationCore (repairSetupTarget key)) =
      bank (inactiveConfigurationCore (repairSetupTarget key)) :=
  inactiveConfigurationClassifierBank_core p bank _ (repairSetup_sources _ _).symm (repairSetup_sources _ _).symm

theorem inactiveConfigurationClassifierBank_blank
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (i : Fin repairT) (hi : RepairBlank i) :
    inactiveConfigurationClassifierBank p bank (inactiveConfigurationCore i) = bank (inactiveConfigurationCore i) :=
  inactiveConfigurationClassifierBank_core p bank i (repairBlank_extraSource i hi .badMask)
    (repairBlank_extraSource i hi .badPhase)

theorem inactiveConfigurationClassifierBank_descriptors
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) (d : RepairDescriptorKey) :
    inactiveConfigurationClassifierBank p bank (inactiveConfigurationCore (repairDescriptorSource d)) =
      bank (inactiveConfigurationCore (repairDescriptorSource d)) :=
  inactiveConfigurationClassifierBank_core p bank _
    (repairNonDescriptor_source (.inr .badMask) trivial d).symm
    (repairNonDescriptor_source (.inr .badPhase) trivial d).symm

theorem inactiveConfigurationClassifierBank_src
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) :
    inactiveConfigurationClassifierBank p bank (inactiveConfigurationCore repairHost.src) =
      bank (inactiveConfigurationCore repairHost.src) :=
  inactiveConfigurationClassifierBank_core p bank _ (repairSetup_source_src _).symm (repairSetup_source_src _).symm

theorem inactiveConfigurationClassifierBank_row
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) :
    inactiveConfigurationClassifierBank p bank (inactiveConfigurationCore (repairSetupSource (.inr .row))) =
      bank (inactiveConfigurationCore (repairSetupSource (.inr .row))) := by
  apply inactiveConfigurationClassifierBank_core <;> simp [repairSetupSource]

theorem inactiveConfigurationClassifierBank_keyMask
    (bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))) :
    inactiveConfigurationClassifierBank p bank (inactiveConfigurationCore (repairSetupSource (.inr .keyMask))) =
      bank (inactiveConfigurationCore (repairSetupSource (.inr .keyMask))) := by
  apply inactiveConfigurationClassifierBank_core <;> simp [repairSetupSource]

theorem RepairPendingMaskData.inactiveConfigurationGenerated (X rb : ℕ) {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin inactiveProfileConfigurationT → List (Fin (A + 4))}
    (data : RepairPendingMaskData p X rb wb wm wp wk R B headers (fun i => bank (inactiveConfigurationCore i))) :
    RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => inactiveConfigurationClassifierBank p bank (inactiveConfigurationCore i)) :=
  data.generated p X rb inactiveConfigurationCore inactiveConfigurationCore_injective

end
end IntegerMultBounds.MathlibTM2.Routing
