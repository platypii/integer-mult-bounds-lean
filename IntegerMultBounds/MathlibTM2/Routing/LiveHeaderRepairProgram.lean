module

public import IntegerMultBounds.MathlibTM2.Routing.ExactSelectiveLive
public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveHeaderFrame

/-! Named live-profile repair and generated-header programs, with fully charged
prices. Numerical parameters occur in prices and input contracts, not program code. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def liveRepairPrice {K : ℕ} (scale wb wm wp wk R B : ℕ) (w : LiveDescriptorWidths)
    (S : Stacks repairLiveT (prime + K)) : ℝ :=
  let D : Stacks repairLiveT (prime + K) := { S with R := liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs }
  let jobs := repairJobs p X rb wb wm wp wk R B
  let C := embStk liveDescriptorCore D
  let installed := metadataInstalled C.R jobs
  (liveDescriptorBatchCost p X hG hK active s repairLiveMode w repairLiveJobs : ℕ) +
    metadataInstallCost C.R jobs + repairDensityCoreCost p X rb R B scale { C with R := installed } +
    metadataCleanCost installed repairTargets + liveDescriptorEraseCost p X repairLiveMode repairLiveJobs

def liveRepairProgram {Q K : ℕ} {P U : Type}
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K) :
    Pr P repairLiveT Q (prime + K) U :=
  .seq (liveDescriptorBatch repairLiveMode repairLiveJobs)
    (.seq (embProg liveDescriptorCore id (repairProgram hQ hA)) (metadataClean (repairLiveJobs.map LiveDescriptorJob.target)))

def liveHeaderRepairPrice {K : ℕ} (scale wb wm wp wk R B Lrow Lwidth : ℕ)
    (w : LiveDescriptorWidths) (S : Stacks repairLiveHeaderT (prime + K)) : ℝ :=
  let G : Stacks repairLiveHeaderT (prime + K) := { S with R := repairHeaderPairBank p X rb R B repairLiveHeaderBank S.R }
  (2 * (14 * (p.wc + p.wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
    liveRepairPrice p X rb hG hK active s scale wb wm wp wk R B w (embStk sharedHeaderCore G) +
    (repairHeaderErasePrice p X rb R B : ℕ)

def liveHeaderRepairProgram {Q K : ℕ} {P U : Type}
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K) :
    Pr P repairLiveHeaderT Q (prime + K) U :=
  .seq (binaryRepairHeaderPairProgram sharedHeaderBinary repairLiveHeaderBank)
    (.seq (embProg sharedHeaderCore id (liveRepairProgram hQ hA))
      (metadataClean (embeddedGeneratedHeaderTargets (liveDescriptorCore (J := 11)))))

end
end IntegerMultBounds.MathlibTM2.Routing
