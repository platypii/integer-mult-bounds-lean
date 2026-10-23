module

public import IntegerMultBounds.MathlibTM2.Routing.LiveInactiveProfileBatch

/-! Partial profile banks compose: generating one job list preserves the pending
contract for another. These facts do not assume the profiles are inactive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {N J A : ℕ}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
  (mode : Fin J → LiveDescriptorMode) (w : LiveDescriptorWidths)

theorem liveProfileBatchBank_append
    (R : Fin (liveInactiveProfileT N J) → List (Fin (A + 4))) (jobs pending : List (Fin J)) :
    liveInactiveProfileBatchBank p X hG hK active s mode w R (jobs ++ pending) =
      liveInactiveProfileBatchBank p X hG hK active s mode w
        (liveInactiveProfileBatchBank p X hG hK active s mode w R jobs) pending := by
  induction jobs generalizing R with
  | nil => rfl
  | cons j jobs ih => exact ih _

theorem liveProfileBatch_pending
    (R : Fin (liveInactiveProfileT N J) → List (Fin (A + 4))) (jobs pending : List (Fin J))
    (hnd : jobs.Nodup)
    (hbank : ∀ r, (∀ j ∈ jobs ++ pending, r ≠ .input j) →
      R (liveInactiveProfileCore (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s mode w r) :
    ∀ r, (∀ j ∈ pending, r ≠ .input j) →
      liveInactiveProfileBatchBank p X hG hK active s mode w R jobs
        (liveInactiveProfileCore (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s mode w r := by
  intro r hr
  by_cases hj : ∃ j ∈ jobs, r = .input j
  · obtain ⟨j, hj, rfl⟩ := hj
    exact liveInactiveProfileBatch_at p X hG hK active s mode w R jobs hnd j hj
  · have hnj : ∀ j ∈ jobs, r ≠ .input j := by simpa only [not_exists, not_and] using hj
    rw [liveInactiveProfileBatch_keep p X hG hK active s mode w R jobs _
      (fun j hj => liveInactiveProfileCore_injective.ne (liveDescriptorAux_injective.ne (hnj j hj)))]
    apply hbank r
    intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact hnj j hj
    · exact hr j hj

end
end IntegerMultBounds.MathlibTM2.Routing
