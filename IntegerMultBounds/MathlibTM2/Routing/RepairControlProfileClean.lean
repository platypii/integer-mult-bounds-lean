module

public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveControlProfiles
public import IntegerMultBounds.MathlibTM2.Routing.RepairTemporaryProfileClean

/-! The eight generated repair profiles share a width; the A profile has more frames.
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

theorem repairControlProfile_length (j : Fin 11) (hj : j ∈ repairControlProfileJobs) :
    ((repairLiveMode j).profileFrames (A := A) p X hG hK active s w.selectorBits).length =
      (if j = 1 ∨ j = 2 then p.wc else p.n) * (w.selectorBits + 3) := by
  rcases List.mem_append.mp hj with hj | hj
  · have he : j = 1 := by simpa using hj
    subst j
    change (affineProfileFrames w.selectorBits
      (affineSourceProfile (repairRotationSources p X hG hK active s .A 0))).length = _
    rw [affineProfileFrames_length]
    simp [affineSourceProfile, repairRotationSlots, Par.wc]
  · have hne : j ≠ 1 := by
      have hh : ∀ j ∈ repairTemporaryProfileJobs, j ≠ (1 : Fin 11) := by decide
      exact hh j hj
    simpa only [hne, false_or] using repairTemporaryProfile_length p X hG hK active s w j hj

theorem repairControlProfileClean_cost (R : Fin T₀ → List (Fin (A + 4)))
    (str : Fin T₀) (hstr : str ∉ liveInactiveProfileTargets repairControlProfileJobs)
    (out : List (Fin (A + 4))) :
    metadataCleanCost
      (Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairControlProfileJobs) str out)
      (liveInactiveProfileTargets repairControlProfileJobs) = 7 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 2 * (2 * (p.wc * (w.selectorBits + 3)) + 2) + 1 := by
  let R' := Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairControlProfileJobs) str out
  have hlen (j : Fin 11) (hj : j ∈ repairControlProfileJobs) :
      (R' (e₀ (liveDescriptorAux (.input j)))).length = (if j = 1 ∨ j = 2 then p.wc else p.n) * (w.selectorBits + 3) := by
    have hne : e₀ (liveDescriptorAux (.input j)) ≠ str := by
      intro he
      exact hstr (List.mem_map.mpr ⟨j, hj, he⟩)
    dsimp only [R']
    rw [Function.update_of_ne hne, liveInactiveProfileBatch_at p X hG hK active s repairLiveMode w R
      repairControlProfileJobs repairControlProfileJobs_nodup j hj]
    exact repairControlProfile_length p X hG hK active s w j hj
  have hcost (ks : List (Fin 11)) (hks : ∀ j ∈ ks, j ∈ repairControlProfileJobs) :
      metadataCleanCost R' (liveInactiveProfileTargets ks) = (ks.map (fun j => 2 * ((if j = 1 ∨ j = 2 then p.wc else p.n) * (w.selectorBits + 3)) + 2)).sum + 1 := by
    induction ks with
    | nil => simp [liveInactiveProfileTargets, metadataCleanCost]
    | cons j ks ih =>
      simp only [liveInactiveProfileTargets, List.map_cons, metadataCleanCost, List.map_cons, List.sum_cons]
      have hi := ih (fun k hk => hks k (by simp [hk]))
      dsimp only [liveInactiveProfileTargets] at hi
      rw [hlen j (hks j (by simp)), hi]
      omega
  rw [hcost repairControlProfileJobs (fun _ h => h)]
  simp [repairControlProfileJobs, repairTemporaryProfileJobs, repairYZProfileJobs, repairActivityProfileJobs,
    repairGeneratedProfileJobs, repairInactiveProfileJobs]
  omega

theorem repairControlProfileClean_exec (body : P → Pr P T₀ Q A U)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hblank : ∀ j ∈ repairControlProfileJobs, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (str : Fin T₀) (hstr : str ∉ liveInactiveProfileTargets repairControlProfileJobs)
    (out : List (Fin (A + 4))) :
    let R := Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairControlProfileJobs) str out
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (liveInactiveProfileTargets repairControlProfileJobs)) (mk v { S with R := R })
        (7 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 2 * (2 * (p.wc * (w.selectorBits + 3)) + 2) + 1) (mk v' { S with R := Function.update S.R str out }) := by
  obtain ⟨v', hu, hx⟩ := liveInactiveProfileClean_exec p X hG hK active s repairLiveMode w body
    repairControlProfileJobs repairControlProfileJobs_nodup v S hblank str hstr out
  rw [repairControlProfileClean_cost p X hG hK active s w S.R str hstr out] at hx
  exact ⟨v', hu, hx⟩

end
end IntegerMultBounds.MathlibTM2.Routing
