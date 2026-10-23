module

public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderWidths
public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthFrame

/-! Width generation preserves descriptor inputs and every invariant needed
by the descriptor-generated exact repair program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ}

theorem liveHeaderWidthBank_keep (rb wy : ℕ)
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (j : Fin repairLiveHeaderT)
    (hr : j ≠ repairLiveHeaderRaw (repairSetupSource (.inr .row)))
    (hm : j ≠ repairLiveHeaderRaw (repairSetupSource (.inr .keyMask))) :
    liveHeaderWidthBank rb wy bank ((fieldCore (N := repairLiveHeaderT)) j) = bank ((fieldCore (N := repairLiveHeaderT)) j) := by
  simp [liveHeaderWidthBank, fieldPairGenerated, fieldCore_injective.eq_iff, hr, hm]

theorem liveHeaderWidthBank_core (rb wy : ℕ)
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (j : Fin repairT)
    (hr : j ≠ repairSetupSource (.inr .row)) (hm : j ≠ repairSetupSource (.inr .keyMask)) :
    liveHeaderWidthBank rb wy bank ((fieldCore (N := repairLiveHeaderT)) (repairLiveHeaderRaw j)) = bank ((fieldCore (N := repairLiveHeaderT)) (repairLiveHeaderRaw j)) :=
  liveHeaderWidthBank_keep rb wy bank _ ((repairLiveHeaderRaw_injective).ne hr) ((repairLiveHeaderRaw_injective).ne hm)

theorem liveHeaderWidthBank_descriptors (rb wy : ℕ)
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (d : RepairDescriptorKey) :
    liveHeaderWidthBank rb wy bank ((fieldCore (N := repairLiveHeaderT)) (repairLiveHeaderRaw (repairDescriptorSource d))) =
      bank ((fieldCore (N := repairLiveHeaderT)) (repairLiveHeaderRaw (repairDescriptorSource d))) :=
  liveHeaderWidthBank_core rb wy bank _
    (repairNonDescriptor_source (.inr .row) trivial d).symm
    (repairNonDescriptor_source (.inr .keyMask) trivial d).symm

theorem liveHeaderWidthBank_targets (rb wy : ℕ)
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (key : RepairSetupKey) :
    liveHeaderWidthBank rb wy bank ((fieldCore (N := repairLiveHeaderT)) (repairLiveHeaderRaw (repairSetupTarget key))) =
      bank ((fieldCore (N := repairLiveHeaderT)) (repairLiveHeaderRaw (repairSetupTarget key))) :=
  liveHeaderWidthBank_core rb wy bank _ (repairSetup_sources _ _).symm (repairSetup_sources _ _).symm

theorem liveHeaderWidthBank_blank (rb wy : ℕ)
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (j : Fin repairT) (hj : RepairBlank j) :
    liveHeaderWidthBank rb wy bank ((fieldCore (N := repairLiveHeaderT)) (repairLiveHeaderRaw j)) = bank ((fieldCore (N := repairLiveHeaderT)) (repairLiveHeaderRaw j)) :=
  liveHeaderWidthBank_core rb wy bank j (repairBlank_extraSource j hj .row)
    (repairBlank_extraSource j hj .keyMask)

theorem liveHeaderWidthBank_aux (rb wy : ℕ)
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (r : LiveDescriptorRole 11) :
    liveHeaderWidthBank rb wy bank (fieldCore (sharedHeaderCore (liveDescriptorAux r))) =
      bank (fieldCore (sharedHeaderCore (liveDescriptorAux r))) := by
  apply liveHeaderWidthBank_keep
  · exact sharedHeaderCore_injective.ne (liveDescriptorCore_aux _ r).symm
  · exact sharedHeaderCore_injective.ne (liveDescriptorCore_aux _ r).symm

theorem liveHeaderWidthBank_work (rb wy : ℕ)
    (bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))) (r : HeaderWorkRole) :
    liveHeaderWidthBank rb wy bank (fieldCore (sharedHeaderWork r)) =
      bank (fieldCore (sharedHeaderWork r)) := by
  apply liveHeaderWidthBank_keep
  · exact (sharedHeaderCore_work _ r).symm
  · exact (sharedHeaderCore_work _ r).symm

theorem LiveDescriptorReady.liveHeaderWidths {p : Par} {X : ℕ}
    {hG : 0 < p.G} {hK : 0 < p.K} {active : Fin p.n → Bool}
    {s : Fin p.n → SlotSource p X} {w : LiveDescriptorWidths} (rb wy : ℕ)
    {bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))}
    (h : LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => bank (fieldCore (sharedHeaderCore i)))) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => liveHeaderWidthBank rb wy bank (fieldCore (sharedHeaderCore i))) := by
  refine ⟨h.bounds, ?_⟩
  intro r
  rw [liveHeaderWidthBank_aux]
  exact h.bank r

variable (p : Par) (X rb : ℕ)

theorem RepairPendingConfigurationData.liveHeaderWidthBank_data {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} {bank : Fin liveHeaderConfigurationT → List (Fin (A + 4))}
    (data : RepairPendingConfigurationData p X rb wb wm wp wk R B headers
      (fun i => bank ((fieldCore (N := repairLiveHeaderT)) (repairLiveHeaderRaw i)))) :
    RepairPendingDescriptorData p X rb wb wm wp wk R B headers
      (fun i => liveHeaderWidthBank rb p.wy bank ((fieldCore (N := repairLiveHeaderT)) (repairLiveHeaderRaw i))) := by
  have hp : (fun i => liveHeaderWidthBank rb p.wy bank ((fieldCore (N := repairLiveHeaderT)) (repairLiveHeaderRaw i))) =
      repairWidthBank rb p.wy (fun i => bank ((fieldCore (N := repairLiveHeaderT)) (repairLiveHeaderRaw i))) := by
    funext i
    simp only [liveHeaderWidthBank, fieldPairGenerated, repairWidthBank,
      Function.update_apply, fieldCore_injective.eq_iff, (repairLiveHeaderRaw_injective).eq_iff]
  rw [hp]
  exact data.widthsGenerated p X rb

end
end IntegerMultBounds.MathlibTM2.Routing
