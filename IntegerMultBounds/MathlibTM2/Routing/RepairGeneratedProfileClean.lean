module

public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveGeneratedProfiles
public import IntegerMultBounds.MathlibTM2.Routing.LiveInactiveProfileClean

/-! All four generated repair profiles have the same frame count and width.
Erase them after a disjoint stream update with a closed cost and exact restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {Q A : ℕ} {P U : Type}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (w : LiveDescriptorWidths)

local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)

theorem repairGeneratedProfile_length (j : Fin 11) (hj : j ∈ repairGeneratedProfileJobs) :
    ((repairLiveMode j).profileFrames (A := A) p X hG hK active s w.selectorBits).length = p.n * (w.selectorBits + 3) := by
  rcases List.mem_append.mp hj with hj | hj
  · rw [repairInactiveProfileJobs_frames p X hG hK active s w j hj, affineProfileFrames_length, List.length_replicate]
  · have he : j = 5 := by simpa using hj
    subst j
    have hmode : repairLiveMode 5 = LiveDescriptorMode.ofKey (some (.Y, 0)) := rfl
    rw [hmode, repairYSourceProfile_frames p X hG hK active s w.selectorBits, affineProfileFrames_length, List.length_ofFn]

theorem repairGeneratedProfileClean_cost (R : Fin T₀ → List (Fin (A + 4)))
    (str : Fin T₀) (hstr : str ∉ liveInactiveProfileTargets repairGeneratedProfileJobs)
    (out : List (Fin (A + 4))) :
    metadataCleanCost
      (Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairGeneratedProfileJobs) str out)
      (liveInactiveProfileTargets repairGeneratedProfileJobs) = 4 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 1 := by
  let R' := Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairGeneratedProfileJobs) str out
  have hlen (j : Fin 11) (hj : j ∈ repairGeneratedProfileJobs) :
      (R' (e₀ (liveDescriptorAux (.input j)))).length = p.n * (w.selectorBits + 3) := by
    have hne : e₀ (liveDescriptorAux (.input j)) ≠ str := by
      intro he
      exact hstr (List.mem_map.mpr ⟨j, hj, he⟩)
    dsimp only [R']
    rw [Function.update_of_ne hne, liveInactiveProfileBatch_at p X hG hK active s repairLiveMode w R
      repairGeneratedProfileJobs repairGeneratedProfileJobs_nodup j hj]
    exact repairGeneratedProfile_length p X hG hK active s w j hj
  have hcost (ks : List (Fin 11)) (hks : ∀ j ∈ ks, j ∈ repairGeneratedProfileJobs) :
      metadataCleanCost R' (liveInactiveProfileTargets ks) = ks.length * (2 * (p.n * (w.selectorBits + 3)) + 2) + 1 := by
    induction ks with
    | nil => simp [liveInactiveProfileTargets, metadataCleanCost]
    | cons j ks ih =>
      simp only [liveInactiveProfileTargets, List.map_cons, metadataCleanCost, List.length_cons]
      have hi := ih (fun k hk => hks k (by simp [hk]))
      dsimp only [liveInactiveProfileTargets] at hi
      rw [hlen j (hks j (by simp)), hi]
      simp only [Nat.add_mul, Nat.one_mul]
      omega
  exact hcost repairGeneratedProfileJobs (fun _ h => h)

theorem repairGeneratedProfileClean_exec (body : P → Pr P T₀ Q A U)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hblank : ∀ j ∈ repairGeneratedProfileJobs, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (str : Fin T₀) (hstr : str ∉ liveInactiveProfileTargets repairGeneratedProfileJobs)
    (out : List (Fin (A + 4))) :
    let R := Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairGeneratedProfileJobs) str out
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (liveInactiveProfileTargets repairGeneratedProfileJobs)) (mk v { S with R := R })
        (4 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 1) (mk v' { S with R := Function.update S.R str out }) := by
  obtain ⟨v', hu, hx⟩ := liveInactiveProfileClean_exec p X hG hK active s repairLiveMode w body
    repairGeneratedProfileJobs repairGeneratedProfileJobs_nodup v S hblank str hstr out
  rw [repairGeneratedProfileClean_cost p X hG hK active s w S.R str hstr out] at hx
  exact ⟨v', hu, hx⟩

end
end IntegerMultBounds.MathlibTM2.Routing
