module

public import IntegerMultBounds.MathlibTM2.Routing.RepairAllSourceProfiles

/-! Profile output writes commute with changes to a disjoint raw core tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {A : ℕ}

theorem liveProfileBatchBank_update_raw
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)
    (R : Fin (liveInactiveProfileT repairT 11) → List (Fin (A + 4)))
    (jobs : List (Fin 11)) (i : Fin repairT) (word : List (Fin (A + 4))) :
    liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w
      (Function.update R (liveZSourceActivity i) word) jobs =
    Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R jobs)
      (liveZSourceActivity i) word := by
  induction jobs generalizing R with
  | nil => rfl
  | cons j jobs ih =>
    simp only [liveInactiveProfileBatchBank, liveInactiveProfileBank]
    have hn : liveZSourceActivity i ≠ liveInactiveProfileCore (liveDescriptorAux (.input j)) :=
      liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux i (.input j))
    rw [Function.update_comm hn, ih]

end
end IntegerMultBounds.MathlibTM2.Routing
