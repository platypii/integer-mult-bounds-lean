module

public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveDescriptorData
public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorClean
public import IntegerMultBounds.MathlibTM2.Routing.RepairInputFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorScratch
public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthFrame

/-! Live-generated descriptor tables do not touch any scratch, installed target or
record-stream tape needed by actual exact repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {A : ℕ} (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem repairLiveBank_core_keep (bank : Fin repairLiveT → List (Fin (A + 4))) (j : Fin repairT)
    (hj : ∀ d, j ≠ repairDescriptorSource d) :
    liveDescriptorBankGenerated p X hG hK active s repairLiveMode bank repairLiveJobs (liveDescriptorCore j) =
      bank (liveDescriptorCore j) := by
  apply liveDescriptorBankGenerated_keep
  intro job hjob
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hjob
  exact liveDescriptorCore_injective.ne (hj (repairDescriptorKey k))

theorem repairLiveBank_blank (bank : Fin repairLiveT → List (Fin (A + 4)))
    (hblank : ∀ j, RepairBlank j → bank (liveDescriptorCore j) = []) :
    ∀ j, RepairBlank j →
      liveDescriptorBankGenerated p X hG hK active s repairLiveMode bank repairLiveJobs (liveDescriptorCore j) = [] := by
  intro j hj
  rw [repairLiveBank_core_keep p X hG hK active s bank j (repairBlank_descriptorSource j hj)]
  exact hblank j hj

theorem repairLiveBank_targets (bank : Fin repairLiveT → List (Fin (A + 4)))
    (hempty : ∀ key, bank (liveDescriptorCore (repairSetupTarget key)) = []) :
    ∀ key, liveDescriptorBankGenerated p X hG hK active s repairLiveMode bank repairLiveJobs
      (liveDescriptorCore (repairSetupTarget key)) = [] := by
  intro key
  rw [repairLiveBank_core_keep p X hG hK active s bank _ (fun d => ?_)]
  · exact hempty key
  · rw [repairDescriptorSource_eq]
    exact (repairSetup_sources _ _).symm

variable {Q : ℕ} {P U : Type}

theorem repairLiveJobs_nodup : (repairLiveJobs.map LiveDescriptorJob.dst).Nodup := by
  rw [repairLiveJobs, List.map_ofFn]
  exact List.nodup_ofFn.mpr repairDescriptorSource_injective

theorem repairLiveClean_exec (body : P → Pr P repairLiveT Q A U)
    (v : HS repairLiveT Q A U) (S : Stacks repairLiveT A) (out : List (Fin (A + 4)))
    (hblank : ∀ key, S.R (liveDescriptorCore (repairDescriptorSource key)) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (repairLiveJobs.map LiveDescriptorJob.target))
        (mk v { S with R := Function.update (liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs) (liveDescriptorCore repairHost.src) out })
        (liveDescriptorEraseCost p X repairLiveMode repairLiveJobs)
        (mk v' { S with R := Function.update S.R (liveDescriptorCore repairHost.src) out }) := by
  apply liveDescriptorClean_exec p X hG hK active s repairLiveMode body repairLiveJobs repairLiveJobs_nodup
  · intro job hj
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    apply liveDescriptorCore_injective.ne
    change repairDescriptorSource (repairDescriptorKey j) ≠ repairHost.src
    rw [repairDescriptorSource_eq]
    exact repairSetup_source_src _
  · intro job hj
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    exact hblank (repairDescriptorKey j)

end
end IntegerMultBounds.MathlibTM2.Routing
