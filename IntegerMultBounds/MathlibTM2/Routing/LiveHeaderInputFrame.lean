module

public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveHeaderFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairInputFrame
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Pending descriptor data, live profile inputs and header workspace readiness
survive record-stream replacement. Placement can therefore precede live repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb : ℕ)

theorem RepairPendingDescriptorData.congr {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    {bank bank' : Fin repairT → List (Fin (A + 4))}
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B headers bank)
    (hkeep : ∀ key, bank' (repairSetupSource key) = bank (repairSetupSource key)) :
    RepairPendingDescriptorData p X rb wb wm wp wk R B headers bank' := by
  have hc (key : SetupKey) : bank' (repairRoutingConfig key) = bank (repairRoutingConfig key) := hkeep (.inl key)
  constructor
  · intro f; rw [hc]; exact data.widths f
  · rw [hc]; exact data.block
  · rw [hc]; exact data.records
  · exact data.block_lt
  · exact data.records_lt
  · intro c k; rw [hc]; exact data.headers c k
  · rw [hkeep]; exact data.row
  · rw [hkeep]; exact data.keyMask
  · rw [hkeep]; exact data.badMask
  · rw [hkeep]; exact data.badPhase
  · rw [hkeep]; exact data.payload
  · exact data.payload_lt
  · rw [hkeep]; exact data.keyLength
  · exact data.keyLength_lt

theorem repairLiveHeaderRaw_injective : Function.Injective repairLiveHeaderRaw :=
  embeddedRepairHeaderRaw_injective _ liveDescriptorCore_injective

theorem RepairPendingDescriptorData.updateLiveHeaderStream {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} {bank : Fin repairLiveHeaderT → List (Fin (A + 4))}
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B headers (fun i => bank (repairLiveHeaderRaw i)))
    (out : List (Fin (A + 4))) :
    RepairPendingDescriptorData p X rb wb wm wp wk R B headers
      (fun i => Function.update bank (repairLiveHeaderRaw repairHost.src) out (repairLiveHeaderRaw i)) := by
  apply data.congr p X rb
  intro key
  exact Function.update_of_ne (repairLiveHeaderRaw_injective.ne (repairSetup_source_src key)) _ _

theorem LiveDescriptorReady.updateHeaderStream {hG : 0 < p.G} {hK : 0 < p.K}
    {active : Fin p.n → Bool} {s : Fin p.n → SlotSource p X} {w : LiveDescriptorWidths}
    {S : Stacks repairLiveHeaderT A}
    (h : LiveDescriptorReady p X hG hK active s repairLiveMode w (embStk sharedHeaderCore S).R)
    (out : List (Fin (A + 4))) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (embStk sharedHeaderCore { S with R := Function.update S.R (repairLiveHeaderRaw repairHost.src) out }).R := by
  change LiveDescriptorReady p X hG hK active s repairLiveMode w
    (embStk sharedHeaderCore { S with R := Function.update S.R (sharedHeaderCore (liveDescriptorCore repairHost.src)) out }).R
  rw [embStk_update_stream sharedHeaderCore sharedHeaderCore_injective]
  exact h.update_core repairHost.src out

theorem liveHeaderWork_updateStream (bank : Fin repairLiveHeaderT → List (Fin (A + 4)))
    (out : List (Fin (A + 4))) (r : HeaderWorkRole) :
    Function.update bank (repairLiveHeaderRaw repairHost.src) out (sharedHeaderWork r) = bank (sharedHeaderWork r) :=
  Function.update_of_ne (sharedHeaderCore_work _ r).symm _ _

theorem liveHeaderBinary_updateStream (bank : Fin repairLiveHeaderT → List (Fin (A + 4)))
    (out : List (Fin (A + 4))) (i : Fin 2) :
    Function.update bank (repairLiveHeaderRaw repairHost.src) out (sharedHeaderBinary i) = bank (sharedHeaderBinary i) :=
  liveHeaderWork_updateStream bank out (.binary i)

end
end IntegerMultBounds.MathlibTM2.Routing
