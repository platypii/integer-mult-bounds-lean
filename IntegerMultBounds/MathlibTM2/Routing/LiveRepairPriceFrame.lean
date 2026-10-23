module

public import IntegerMultBounds.MathlibTM2.Routing.LiveHeaderRepairProgram
public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorBankFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairPriceFrame

/-! Generated live-profile repair has a price independent of its record stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {K : ℕ}
variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem liveRepairPrice_eq_raw (scale wb wm wp wk R B : ℕ) (w : LiveDescriptorWidths)
    (S : Stacks repairLiveT (prime + K)) :
    liveRepairPrice p X rb hG hK active s scale wb wm wp wk R B w S =
      (liveDescriptorBatchCost p X hG hK active s repairLiveMode w repairLiveJobs : ℕ) +
        repairRawPrice p X rb wb wm wp wk R B scale
          (embStk liveDescriptorCore { S with R := liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs }) +
        liveDescriptorEraseCost p X repairLiveMode repairLiveJobs := by
  simp only [liveRepairPrice, repairRawPrice, add_assoc]

theorem liveRepairPrice_updateStream (scale wb wm wp wk R B : ℕ) (w : LiveDescriptorWidths)
    (S : Stacks repairLiveT (prime + K)) (out : List (Fin (prime + K + 4)))
    (hblank : ∀ j, RepairBlank j → S.R (liveDescriptorCore j) = []) :
    liveRepairPrice p X rb hG hK active s scale wb wm wp wk R B w
        { S with R := Function.update S.R (liveDescriptorCore repairHost.src) out } =
      liveRepairPrice p X rb hG hK active s scale wb wm wp wk R B w S := by
  have hstr : ∀ job ∈ repairLiveJobs,
      liveDescriptorCore repairHost.src ≠ liveDescriptorCore (J := 11) job.dst := by
    intro job hj
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    apply liveDescriptorCore_injective.ne
    change repairHost.src ≠ repairDescriptorSource (repairDescriptorKey j)
    rw [repairDescriptorSource_eq]
    exact (repairSetup_source_src _).symm
  have hgen := liveDescriptorBankGenerated_update p X hG hK active s repairLiveMode S.R repairLiveJobs
    (liveDescriptorCore repairHost.src) out hstr
  let D : Stacks repairLiveT (prime + K) := { S with R := liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs }
  have hb : ∀ j, RepairBlank j → (embStk liveDescriptorCore D).R j = [] := by
    intro j hj
    exact repairLiveBank_blank p X hG hK active s S.R hblank j hj
  rw [liveRepairPrice_eq_raw, liveRepairPrice_eq_raw]
  dsimp only
  rw [hgen]
  change (_ : ℝ) + repairRawPrice p X rb wb wm wp wk R B scale
    (embStk liveDescriptorCore { D with R := Function.update D.R (liveDescriptorCore repairHost.src) out }) + _ = _
  rw [embStk_update_stream liveDescriptorCore liveDescriptorCore_injective,
    repairRawPrice_updateStream p X rb wb wm wp wk R B scale _ out hb]

end
end IntegerMultBounds.MathlibTM2.Routing
