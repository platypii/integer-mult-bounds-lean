module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorBatch
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorContents
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorFrame

/-! The eleven actual repair descriptors execute through a single shared live
workspace, including empty tables. Exact descriptor contents and preservation
of all other configuration inputs follow from the initial common bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

abbrev repairLiveT := liveDescriptorT repairT 11

def repairLiveMode (j : Fin 11) : LiveDescriptorMode := LiveDescriptorMode.ofKey (repairDescriptorKey j)

def repairLiveJobs : List (LiveDescriptorJob repairT 11) :=
  List.ofFn (fun j => ⟨j, repairDescriptorSource (repairDescriptorKey j)⟩)

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem repairLiveBankCost_le (hGK : p.G < p.K) (w : LiveDescriptorWidths)
    (n slots : ℕ)
    (hfields : IntegerMultBounds.MathlibTM2.Layer.CompactDigits.fieldsLen (selectiveLen p X) = n)
    (hn : p.n ≤ slots) (hgroup : p.n * p.G ≤ slots)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j)) :
    liveDescriptorBatchCost p X hG hK active s repairLiveMode w repairLiveJobs ≤
      11 * (14 * w.coordinateBits + 16 + LiveDescriptorMode.uniformBackendBudget n slots
        w.indexBits w.groupBits w.strideBits w.selectorBits w.widthBits) + 1 := by
  simpa only [repairLiveJobs, List.length_ofFn] using
    liveDescriptorBatchCost_uniform p X hG hK active s repairLiveMode w hGK n slots
      hfields hn hgroup (fun j => (hfit j).coordinate_fits) repairLiveJobs

theorem repairLiveBank_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P repairLiveT Q A U) (hGK : p.G < p.K) (w : LiveDescriptorWidths)
    (v : HS repairLiveT Q A U) (S : Stacks repairLiveT A)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, S.R (liveDescriptorAux r) = liveDescriptorData p X hG hK active s repairLiveMode w r) :
    ∃ (v' : HS repairLiveT Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ liveDescriptorBatchCost p X hG hK active s repairLiveMode w repairLiveJobs ∧
      Exec body (liveDescriptorBatch repairLiveMode repairLiveJobs) (mk v S) steps
        (mk v' { S with R := liveDescriptorBankGenerated p X hG hK active s repairLiveMode S.R repairLiveJobs }) :=
  liveDescriptorBatch_exec p X hG hK active s repairLiveMode w body hGK repairLiveJobs v S ⟨hfit, hbank⟩

theorem repairLiveBank_contents {A : ℕ}
    (R : Fin repairLiveT → List (Fin (A + 4))) (j : Fin 11) :
    liveDescriptorBankGenerated p X hG hK active s repairLiveMode R repairLiveJobs
      (liveDescriptorCore (repairDescriptorSource (repairDescriptorKey j))) =
      repairDescriptorWord p X hG hK active s (repairDescriptorKey j) ++
        R (liveDescriptorCore (repairDescriptorSource (repairDescriptorKey j))) := by
  have hn : (repairLiveJobs.map LiveDescriptorJob.dst).Nodup := by
    rw [repairLiveJobs, List.map_ofFn]
    exact List.nodup_ofFn.mpr repairDescriptorSource_injective
  have hj : (⟨j, repairDescriptorSource (repairDescriptorKey j)⟩ : LiveDescriptorJob repairT 11) ∈ repairLiveJobs :=
    List.mem_ofFn.mpr ⟨j, rfl⟩
  have he := liveDescriptorBankGenerated_at p X hG hK active s repairLiveMode R repairLiveJobs hn _ hj
  simpa only [repairLiveMode, LiveDescriptorMode.key_ofKey] using he

theorem repairLiveBank_at {A : ℕ} (R : Fin repairLiveT → List (Fin (A + 4)))
    (hblank : ∀ key, R (liveDescriptorCore (repairDescriptorSource key)) = []) (key : RepairDescriptorKey) :
    liveDescriptorBankGenerated p X hG hK active s repairLiveMode R repairLiveJobs
      (liveDescriptorCore (repairDescriptorSource key)) = repairDescriptorWord p X hG hK active s key := by
  obtain ⟨j, rfl⟩ := repairDescriptorKey_covers key
  rw [repairLiveBank_contents, hblank, List.append_nil]

theorem repairLiveBank_keep {A : ℕ} (R : Fin repairLiveT → List (Fin (A + 4)))
    (key : RepairSetupKey) (hk : RepairNonDescriptor key) :
    liveDescriptorBankGenerated p X hG hK active s repairLiveMode R repairLiveJobs
      (liveDescriptorCore (repairSetupSource key)) = R (liveDescriptorCore (repairSetupSource key)) := by
  apply liveDescriptorBankGenerated_keep
  intro job hj
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
  exact liveDescriptorCore_injective.ne (repairNonDescriptor_source key hk (repairDescriptorKey j))

theorem repairLiveBank_aux {A : ℕ} (R : Fin repairLiveT → List (Fin (A + 4))) (r : LiveDescriptorRole 11) :
    liveDescriptorBankGenerated p X hG hK active s repairLiveMode R repairLiveJobs (liveDescriptorAux r) = R (liveDescriptorAux r) :=
  liveDescriptorBankGenerated_aux p X hG hK active s repairLiveMode R repairLiveJobs r

end
end IntegerMultBounds.MathlibTM2.Routing
