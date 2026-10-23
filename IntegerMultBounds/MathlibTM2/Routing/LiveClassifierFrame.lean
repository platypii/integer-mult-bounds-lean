module

public import IntegerMultBounds.MathlibTM2.Routing.RepairClassifierPair
public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderConfigurationFrame
public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderWidthFrame

/-! Generated classifiers preserve every other exact-repair input: descriptors,
widths, scratch, installation destinations and the original record stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par)

def liveHeaderConfigurationClassifierBank (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) :=
  repairClassifierGenerated p liveHeaderConfigurationCore bank

theorem liveHeaderConfigurationClassifierBank_keep
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (i : Fin liveHeaderConfigurationT)
    (ht : i ≠ liveHeaderConfigurationCore (repairSetupSource (.inr .badMask)))
    (hp : i ≠ liveHeaderConfigurationCore (repairSetupSource (.inr .badPhase))) :
    liveHeaderConfigurationClassifierBank p bank i = bank i := by
  simp [liveHeaderConfigurationClassifierBank, repairClassifierGenerated, ht, hp]

theorem liveHeaderConfigurationClassifierBank_core
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (i : Fin repairT)
    (ht : i ≠ repairSetupSource (.inr .badMask)) (hp : i ≠ repairSetupSource (.inr .badPhase)) :
    liveHeaderConfigurationClassifierBank p bank (liveHeaderConfigurationCore i) = bank (liveHeaderConfigurationCore i) :=
  liveHeaderConfigurationClassifierBank_keep p bank _ (liveHeaderConfigurationCore_injective.ne ht)
    (liveHeaderConfigurationCore_injective.ne hp)

theorem liveHeaderConfigurationClassifierBank_widthAux
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (i : Fin 6) :
    liveHeaderConfigurationClassifierBank p bank (fieldAux i) = bank (fieldAux i) :=
  liveHeaderConfigurationClassifierBank_keep p bank _ (fieldCore_aux _ i).symm (fieldCore_aux _ i).symm

theorem liveHeaderConfigurationClassifierBank_liveAux
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (r : LiveDescriptorRole 11) :
    liveHeaderConfigurationClassifierBank p bank (fieldCore (sharedHeaderCore (liveDescriptorAux r))) =
      bank (fieldCore (sharedHeaderCore (liveDescriptorAux r))) := by
  apply liveHeaderConfigurationClassifierBank_keep
  · exact fieldCore_injective.ne (sharedHeaderCore_injective.ne (liveDescriptorCore_aux _ r).symm)
  · exact fieldCore_injective.ne (sharedHeaderCore_injective.ne (liveDescriptorCore_aux _ r).symm)

theorem liveHeaderConfigurationClassifierBank_headerWork
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (r : HeaderWorkRole) :
    liveHeaderConfigurationClassifierBank p bank (fieldCore (sharedHeaderWork r)) =
      bank (fieldCore (sharedHeaderWork r)) := by
  apply liveHeaderConfigurationClassifierBank_keep
  · exact fieldCore_injective.ne (sharedHeaderCore_work _ r).symm
  · exact fieldCore_injective.ne (sharedHeaderCore_work _ r).symm

theorem liveHeaderConfigurationClassifierBank_targets
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (key : RepairSetupKey) :
    liveHeaderConfigurationClassifierBank p bank (liveHeaderConfigurationCore (repairSetupTarget key)) =
      bank (liveHeaderConfigurationCore (repairSetupTarget key)) :=
  liveHeaderConfigurationClassifierBank_core p bank _ (repairSetup_sources _ _).symm (repairSetup_sources _ _).symm

theorem liveHeaderConfigurationClassifierBank_blank
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (i : Fin repairT) (hi : RepairBlank i) :
    liveHeaderConfigurationClassifierBank p bank (liveHeaderConfigurationCore i) = bank (liveHeaderConfigurationCore i) :=
  liveHeaderConfigurationClassifierBank_core p bank i (repairBlank_extraSource i hi .badMask)
    (repairBlank_extraSource i hi .badPhase)

theorem liveHeaderConfigurationClassifierBank_descriptors
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (d : RepairDescriptorKey) :
    liveHeaderConfigurationClassifierBank p bank (liveHeaderConfigurationCore (repairDescriptorSource d)) =
      bank (liveHeaderConfigurationCore (repairDescriptorSource d)) :=
  liveHeaderConfigurationClassifierBank_core p bank _
    (repairNonDescriptor_source (.inr .badMask) trivial d).symm
    (repairNonDescriptor_source (.inr .badPhase) trivial d).symm

theorem liveHeaderConfigurationClassifierBank_src
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) :
    liveHeaderConfigurationClassifierBank p bank (liveHeaderConfigurationCore repairHost.src) =
      bank (liveHeaderConfigurationCore repairHost.src) :=
  liveHeaderConfigurationClassifierBank_core p bank _ (repairSetup_source_src _).symm (repairSetup_source_src _).symm

theorem liveHeaderConfigurationClassifierBank_row
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) :
    liveHeaderConfigurationClassifierBank p bank (liveHeaderConfigurationCore (repairSetupSource (.inr .row))) =
      bank (liveHeaderConfigurationCore (repairSetupSource (.inr .row))) := by
  apply liveHeaderConfigurationClassifierBank_core <;> simp [repairSetupSource]

theorem liveHeaderConfigurationClassifierBank_keyMask
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) :
    liveHeaderConfigurationClassifierBank p bank (liveHeaderConfigurationCore (repairSetupSource (.inr .keyMask))) =
      bank (liveHeaderConfigurationCore (repairSetupSource (.inr .keyMask))) := by
  apply liveHeaderConfigurationClassifierBank_core <;> simp [repairSetupSource]

theorem LiveDescriptorReady.liveClassifiers {X : ℕ} {hG : 0 < p.G} {hK : 0 < p.K}
    {active : Fin p.n → Bool} {s : Fin p.n → SlotSource p X} {w : LiveDescriptorWidths}
    {bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))}
    (h : LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => bank (fieldCore (sharedHeaderCore i)))) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => liveHeaderConfigurationClassifierBank p bank (fieldCore (sharedHeaderCore i))) := by
  refine ⟨h.bounds, ?_⟩
  intro r
  rw [liveHeaderConfigurationClassifierBank_liveAux]
  exact h.bank r

theorem RepairPendingMaskData.liveHeaderConfigurationGenerated (X rb : ℕ) {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool}
    {bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))}
    (data : RepairPendingMaskData p X rb wb wm wp wk R B headers (fun i => bank (liveHeaderConfigurationCore i))) :
    RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => liveHeaderConfigurationClassifierBank p bank (liveHeaderConfigurationCore i)) :=
  data.generated p X rb liveHeaderConfigurationCore liveHeaderConfigurationCore_injective

end
end IntegerMultBounds.MathlibTM2.Routing
