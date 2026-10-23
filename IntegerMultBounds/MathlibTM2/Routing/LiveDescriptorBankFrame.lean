module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorBatch

/-! Descriptor generation commutes with updates to an unrelated stream tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {N J A : ℕ}

theorem liveDescriptorBankGenerated_update (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (mode : Fin J → LiveDescriptorMode)
    (bank : Fin (liveDescriptorT N J) → List (Fin (A + 4)))
    (jobs : List (LiveDescriptorJob N J)) (str : Fin (liveDescriptorT N J)) (out : List (Fin (A + 4)))
    (hstr : ∀ job ∈ jobs, str ≠ liveDescriptorCore (J := J) job.dst) :
    liveDescriptorBankGenerated p X hG hK active s mode (Function.update bank str out) jobs =
      Function.update (liveDescriptorBankGenerated p X hG hK active s mode bank jobs) str out := by
  induction jobs generalizing bank with
  | nil => rfl
  | cons job jobs ih =>
    have hne := hstr job (by simp)
    have hc : Function.update (Function.update bank str out) (liveDescriptorCore (J := J) job.dst)
        (repairDescriptorWord p X hG hK active s (mode job.index).key ++
          (Function.update bank str out) (liveDescriptorCore (J := J) job.dst)) =
        Function.update (Function.update bank (liveDescriptorCore (J := J) job.dst)
          (repairDescriptorWord p X hG hK active s (mode job.index).key ++ bank (liveDescriptorCore (J := J) job.dst))) str out := by
      rw [Function.update_of_ne hne.symm]
      exact Function.update_comm hne out _ bank
    rw [liveDescriptorBankGenerated, liveDescriptorBankGenerated, hc]
    exact ih _ (fun j hj => hstr j (by simp [hj]))

end
end IntegerMultBounds.MathlibTM2.Routing
