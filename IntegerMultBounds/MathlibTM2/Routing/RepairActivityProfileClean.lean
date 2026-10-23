module

public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveActivityProfiles
public import IntegerMultBounds.MathlibTM2.Routing.RepairGeneratedProfileClean

/-! All five generated repair profiles have the same frame count and width.
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

theorem repairActivityProfile_length (j : Fin 11) (hj : j ∈ repairActivityProfileJobs) :
    ((repairLiveMode j).profileFrames (A := A) p X hG hK active s w.selectorBits).length = p.n * (w.selectorBits + 3) := by
  rcases List.mem_append.mp hj with hj | hj
  · have he : j = 3 := by simpa using hj
    subst j
    change (affineProfileFrames w.selectorBits
      (affineSourceProfile (repairAffineSources p X hG hK active s (some (.Z, 0))))).length = _
    rw [affineProfileFrames_length]
    simp [affineSourceProfile]
  · exact repairGeneratedProfile_length p X hG hK active s w j hj

theorem repairActivityProfileClean_cost (R : Fin T₀ → List (Fin (A + 4)))
    (str : Fin T₀) (hstr : str ∉ liveInactiveProfileTargets repairActivityProfileJobs)
    (out : List (Fin (A + 4))) :
    metadataCleanCost
      (Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairActivityProfileJobs) str out)
      (liveInactiveProfileTargets repairActivityProfileJobs) = 5 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 1 := by
  let R' := Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairActivityProfileJobs) str out
  have hlen (j : Fin 11) (hj : j ∈ repairActivityProfileJobs) :
      (R' (e₀ (liveDescriptorAux (.input j)))).length = p.n * (w.selectorBits + 3) := by
    have hne : e₀ (liveDescriptorAux (.input j)) ≠ str := by
      intro he
      exact hstr (List.mem_map.mpr ⟨j, hj, he⟩)
    dsimp only [R']
    rw [Function.update_of_ne hne, liveInactiveProfileBatch_at p X hG hK active s repairLiveMode w R
      repairActivityProfileJobs repairActivityProfileJobs_nodup j hj]
    exact repairActivityProfile_length p X hG hK active s w j hj
  have hcost (ks : List (Fin 11)) (hks : ∀ j ∈ ks, j ∈ repairActivityProfileJobs) :
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
  exact hcost repairActivityProfileJobs (fun _ h => h)

theorem repairActivityProfileClean_exec (body : P → Pr P T₀ Q A U)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hblank : ∀ j ∈ repairActivityProfileJobs, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (str : Fin T₀) (hstr : str ∉ liveInactiveProfileTargets repairActivityProfileJobs)
    (out : List (Fin (A + 4))) :
    let R := Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairActivityProfileJobs) str out
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (liveInactiveProfileTargets repairActivityProfileJobs)) (mk v { S with R := R })
        (5 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 1) (mk v' { S with R := Function.update S.R str out }) := by
  obtain ⟨v', hu, hx⟩ := liveInactiveProfileClean_exec p X hG hK active s repairLiveMode w body
    repairActivityProfileJobs repairActivityProfileJobs_nodup v S hblank str hstr out
  rw [repairActivityProfileClean_cost p X hG hK active s w S.R str hstr out] at hx
  exact ⟨v', hu, hx⟩

end
end IntegerMultBounds.MathlibTM2.Routing
