module

public import IntegerMultBounds.MathlibTM2.Routing.EmbeddedRepairHeaderClean
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveDescriptorData

/-! Header generation preserves the live descriptor auxiliary bank, raw repair
scratch and all non-header configuration. Canonical-header data follows from
the same initial pending-descriptor data; no new descriptor inputs are supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev repairLiveHeaderT := sharedHeaderT repairLiveT
def repairLiveHeaderRaw (i : Fin repairT) : Fin repairLiveHeaderT := embeddedRepairHeaderRaw (liveDescriptorCore (J := 11)) i
def repairLiveHeaderBank (c : Fin 2) : RepairHeaderReg → Fin repairLiveHeaderT :=
  embeddedRepairHeaderBank (liveDescriptorCore (N := repairT) (J := 11)) c

@[simp] theorem repairLiveHeaderBank_header (c : Fin 2) (k : Fin 5) :
    repairLiveHeaderBank c (.exchange (.base (.header k))) = repairLiveHeaderRaw (repairRoutingConfig (.header c k)) := rfl

variable {A : ℕ} (p : Par) (X rb R B : ℕ)

theorem repairLiveHeaderPair_raw_keep (tapes : Fin repairLiveHeaderT → List (Fin (A + 4)))
    (i : Fin repairT) (hi : ∀ c k, i ≠ repairRoutingConfig (.header c k)) :
    repairHeaderPairBank p X rb R B repairLiveHeaderBank tapes (repairLiveHeaderRaw i) = tapes (repairLiveHeaderRaw i) :=
  embeddedRepairHeaderPair_raw_keep _ liveDescriptorCore_injective p X rb R B tapes i hi

theorem repairLiveHeaderPair_aux (tapes : Fin repairLiveHeaderT → List (Fin (A + 4))) (r : LiveDescriptorRole 11) :
    repairHeaderPairBank p X rb R B repairLiveHeaderBank tapes (sharedHeaderCore (liveDescriptorAux r)) =
      tapes (sharedHeaderCore (liveDescriptorAux r)) :=
  embeddedRepairHeaderPair_keep _ p X rb R B tapes (liveDescriptorAux r)
    (fun c k => (liveDescriptorCore_aux (repairRoutingConfig (.header c k)) r).symm)

theorem repairLiveHeaderPair_targets (tapes : Fin repairLiveHeaderT → List (Fin (A + 4))) (key : RepairSetupKey) :
    repairHeaderPairBank p X rb R B repairLiveHeaderBank tapes (repairLiveHeaderRaw (repairSetupTarget key)) =
      tapes (repairLiveHeaderRaw (repairSetupTarget key)) :=
  repairLiveHeaderPair_raw_keep p X rb R B tapes _ (fun c k => (repairSetup_sources (.inl (.header c k)) key).symm)

theorem repairLiveHeaderPair_src (tapes : Fin repairLiveHeaderT → List (Fin (A + 4))) :
    repairHeaderPairBank p X rb R B repairLiveHeaderBank tapes (repairLiveHeaderRaw repairHost.src) = tapes (repairLiveHeaderRaw repairHost.src) :=
  repairLiveHeaderPair_raw_keep p X rb R B tapes _ (fun c k => (repairSetup_source_src (.inl (.header c k))).symm)

theorem repairLiveHeaderPair_descriptors (tapes : Fin repairLiveHeaderT → List (Fin (A + 4))) (key : RepairDescriptorKey) :
    repairHeaderPairBank p X rb R B repairLiveHeaderBank tapes (repairLiveHeaderRaw (repairDescriptorSource key)) =
      tapes (repairLiveHeaderRaw (repairDescriptorSource key)) := by
  apply repairLiveHeaderPair_raw_keep
  intro c k
  cases key with
  | none => simp [repairDescriptorSource, repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]
  | some pair =>
    obtain ⟨off, j⟩ := pair
    simp [repairDescriptorSource, repairSetupSource, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]

theorem repairLiveHeaderPair_blank (tapes : Fin repairLiveHeaderT → List (Fin (A + 4))) (i : Fin repairT) (hi : RepairBlank i) :
    repairHeaderPairBank p X rb R B repairLiveHeaderBank tapes (repairLiveHeaderRaw i) = tapes (repairLiveHeaderRaw i) :=
  repairLiveHeaderPair_raw_keep p X rb R B tapes i (repairBlank_headerSource i hi)

theorem LiveDescriptorReady.liveHeaders {hG : 0 < p.G} {hK : 0 < p.K}
    {active : Fin p.n → Bool} {s : Fin p.n → SlotSource p X} {w : LiveDescriptorWidths}
    {tapes : Fin repairLiveHeaderT → List (Fin (A + 4))}
    (h : LiveDescriptorReady p X hG hK active s repairLiveMode w (fun i => tapes (sharedHeaderCore i))) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => repairHeaderPairBank p X rb R B repairLiveHeaderBank tapes (sharedHeaderCore i)) := by
  refine ⟨h.bounds, ?_⟩
  intro r
  rw [repairLiveHeaderPair_aux]
  exact h.bank r

theorem RepairPendingDescriptorData.liveHeaders {wb wm wp wk : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {tapes : Fin repairLiveHeaderT → List (Fin (A + 4))}
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B headers (fun i => tapes (repairLiveHeaderRaw i))) :
    RepairPendingDescriptorData p X rb wb wm wp wk R B (repairCanonicalHeaders p X rb R B)
      (fun i => repairHeaderPairBank p X rb R B repairLiveHeaderBank tapes (repairLiveHeaderRaw i)) :=
  RepairPendingDescriptorData.embeddedHeaders _ liveDescriptorCore_injective p X rb R B data

end
end IntegerMultBounds.MathlibTM2.Routing
