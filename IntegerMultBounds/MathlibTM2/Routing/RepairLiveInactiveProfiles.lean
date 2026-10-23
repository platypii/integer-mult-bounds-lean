module

public import IntegerMultBounds.MathlibTM2.Routing.LiveInactiveProfileBatch
public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveDescriptorBank

/-! The three inactive repair profiles execute through one shared workspace.
Their input tapes start blank; all remaining live inputs are preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

def repairInactiveProfileJobs : List (Fin 11) := [4, 6, 10]

theorem repairInactiveProfileJobs_nodup : repairInactiveProfileJobs.Nodup := by decide

variable {Q A : ℕ} {P U : Type}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)

theorem repairInactiveProfileJobs_frames (j : Fin 11) (hj : j ∈ repairInactiveProfileJobs) :
    (repairLiveMode j).profileFrames (A := A) p X hG hK active s w.selectorBits =
      affineProfileFrames w.selectorBits (List.replicate p.n (false, 0)) := by
  simp only [repairInactiveProfileJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl
  · exact repairInactiveProfile_frames p X hG hK active s .Z (Or.inl rfl) w.selectorBits
  · exact repairInactiveProfile_frames p X hG hK active s .Y (Or.inr (Or.inl rfl)) w.selectorBits
  · exact repairInactiveProfile_frames p X hG hK active s .X (Or.inr (Or.inr rfl)) w.selectorBits

theorem repairLiveInactiveProfiles_exec
    (body : P → Pr P (liveInactiveProfileT repairT 11) Q A U)
    (Lc : ℕ) (hn : p.n < 2 ^ Lc) (hselector : w.selectorBits < 2 ^ w.widthBits)
    (v : HS (liveInactiveProfileT repairT 11) Q A U) (S : Stacks (liveInactiveProfileT repairT 11) A)
    (hwidth : S.R (liveInactiveProfileCore (liveDescriptorAux .selectorBits)) = binSyms w.widthBits w.selectorBits)
    (hinput : ∀ j ∈ repairInactiveProfileJobs, S.R (liveInactiveProfileCore (liveDescriptorAux (.input j))) = [])
    (hcount : S.R (liveInactiveProfileAux 0) = binSyms Lc p.n)
    (hscratch : ∀ i : Fin 7, i ≠ 0 → S.R (liveInactiveProfileAux i) = []) :
    ∃ (v' : HS (liveInactiveProfileT repairT 11) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ 3 * binaryInactiveProfileCost w.widthBits Lc w.selectorBits p.n + 1 ∧
      Exec body (liveInactiveProfileBatch repairInactiveProfileJobs) (mk v S) steps
        (mk v' { S with R := liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairInactiveProfileJobs }) :=
  liveInactiveProfileBatch_exec p X hG hK active s repairLiveMode w body repairInactiveProfileJobs
    repairInactiveProfileJobs_nodup Lc hn (repairInactiveProfileJobs_frames p X hG hK active s w)
    hselector v S hwidth hinput hcount hscratch

theorem repairLiveInactiveProfiles_ready
    (R : Fin (liveInactiveProfileT repairT 11) → List (Fin (A + 4)))
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (hbank : ∀ r, (∀ j ∈ repairInactiveProfileJobs, r ≠ .input j) →
      R (liveInactiveProfileCore (liveDescriptorAux r)) = liveDescriptorData p X hG hK active s repairLiveMode w r) :
    LiveDescriptorReady p X hG hK active s repairLiveMode w
      (fun i => liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairInactiveProfileJobs (liveInactiveProfileCore i)) :=
  liveInactiveProfileBatch_ready p X hG hK active s repairLiveMode w R repairInactiveProfileJobs
    repairInactiveProfileJobs_nodup hfit hbank

theorem repairLiveInactiveProfiles_core
    (R : Fin (liveInactiveProfileT repairT 11) → List (Fin (A + 4))) (i : Fin repairT) :
    liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairInactiveProfileJobs
      (liveInactiveProfileCore (liveDescriptorCore i)) = R (liveInactiveProfileCore (liveDescriptorCore i)) := by
  apply liveInactiveProfileBatch_keep
  intro j _
  exact liveInactiveProfileCore_injective.ne (liveDescriptorCore_aux i (.input j))

theorem repairLiveInactiveProfiles_aux
    (R : Fin (liveInactiveProfileT repairT 11) → List (Fin (A + 4))) (i : Fin 7) :
    liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairInactiveProfileJobs
      (liveInactiveProfileAux i) = R (liveInactiveProfileAux i) := by
  apply liveInactiveProfileBatch_keep
  intro j _
  exact liveInactiveProfileAux_core _ _

end
end IntegerMultBounds.MathlibTM2.Routing
