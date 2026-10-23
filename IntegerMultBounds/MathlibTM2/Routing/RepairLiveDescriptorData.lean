module

public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveDescriptorBank
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorData

/-! The initial R2 contract omits all eleven raw descriptors. Live profile descriptor
compilation establishes the complete existing setup-data contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem RepairPendingDescriptorData.liveGenerated {wb wm wp wk R B : ℕ}
    {headers : Fin 2 → Fin 5 → List Bool} 
    {bank : Fin repairLiveT → List (Fin (A + 4))}
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B headers
      (fun i => bank (liveDescriptorCore i)))
    (hblank : ∀ d, bank (liveDescriptorCore (repairDescriptorSource d)) = []) :
    RepairSetupData p X rb hG hK active s wb wm wp wk R B headers
      (fun i => liveDescriptorBankGenerated p X hG hK active s repairLiveMode bank repairLiveJobs (liveDescriptorCore i)) := by
  have hkeep := repairLiveBank_keep p X hG hK active s bank
  constructor
  · constructor
    · intro f
      change (liveDescriptorBankGenerated p X hG hK active s repairLiveMode bank repairLiveJobs (liveDescriptorCore (repairSetupSource (.inl (.field f))))).length = _
      rw [hkeep (.inl (.field f)) trivial]; exact data.widths f
    · intro off k
      exact repairLiveBank_at p X hG hK active s bank hblank (some (off, k))
    · change liveDescriptorBankGenerated p X hG hK active s repairLiveMode bank repairLiveJobs (liveDescriptorCore (repairSetupSource (.inl .block))) = _
      rw [hkeep (.inl .block) trivial]; exact data.block
    · change liveDescriptorBankGenerated p X hG hK active s repairLiveMode bank repairLiveJobs (liveDescriptorCore (repairSetupSource (.inl .records))) = _
      rw [hkeep (.inl .records) trivial]; exact data.records
    · exact data.block_lt
    · exact data.records_lt
    · intro c k
      change liveDescriptorBankGenerated p X hG hK active s repairLiveMode bank repairLiveJobs (liveDescriptorCore (repairSetupSource (.inl (.header c k)))) = _
      rw [hkeep (.inl (.header c k)) trivial]; exact data.headers c k
  · rw [hkeep (.inr .row) trivial]; exact data.row
  · exact repairLiveBank_at p X hG hK active s bank hblank none
  · rw [hkeep (.inr .keyMask) trivial]; exact data.keyMask
  · rw [hkeep (.inr .badMask) trivial]; exact data.badMask
  · rw [hkeep (.inr .badPhase) trivial]; exact data.badPhase
  · rw [hkeep (.inr .payload) trivial]; exact data.payload
  · exact data.payload_lt
  · rw [hkeep (.inr .keyLength) trivial]; exact data.keyLength
  · exact data.keyLength_lt

end
end IntegerMultBounds.MathlibTM2.Routing
