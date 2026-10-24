module

public import IntegerMultBounds.MathlibTM2.Routing.RepairAllSourceProfiles
public import IntegerMultBounds.MathlibTM2.Routing.RepairControlProfileClean
public import IntegerMultBounds.MathlibTM2.Routing.RepairTemporaryProfileClean

/-! All eleven generated profiles share a frame width; the two A profiles have more frames.
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

theorem repairAllSourceProfile_length (j : Fin 11) (hj : j ∈ repairAllSourceProfileJobs) :
    ((repairLiveMode j).profileFrames (A := A) p X hG hK active s w.selectorBits).length =
      (if j = 1 ∨ j = 2 then p.wc else p.n) * (w.selectorBits + 3) := by
  rcases List.mem_append.mp hj with hj | hj
  · have he : j = 0 ∨ j = 9 := by simpa using hj
    rcases he with rfl | rfl <;>
      change (affineProfileFrames w.selectorBits (affineSourceProfile _)).length = _
    all_goals rw [affineProfileFrames_length]
    all_goals simp [affineSourceProfile]
  · exact repairControlProfile_length p X hG hK active s w j hj

theorem repairAllSourceProfileClean_cost (R : Fin T₀ → List (Fin (A + 4)))
    (str : Fin T₀) (hstr : str ∉ liveInactiveProfileTargets repairAllSourceProfileJobs)
    (out : List (Fin (A + 4))) :
    metadataCleanCost
      (Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairAllSourceProfileJobs) str out)
      (liveInactiveProfileTargets repairAllSourceProfileJobs) = 9 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 2 * (2 * (p.wc * (w.selectorBits + 3)) + 2) + 1 := by
  let R' := Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairAllSourceProfileJobs) str out
  have hlen (j : Fin 11) (hj : j ∈ repairAllSourceProfileJobs) :
      (R' (e₀ (liveDescriptorAux (.input j)))).length = (if j = 1 ∨ j = 2 then p.wc else p.n) * (w.selectorBits + 3) := by
    have hne : e₀ (liveDescriptorAux (.input j)) ≠ str := by
      intro he
      exact hstr (List.mem_map.mpr ⟨j, hj, he⟩)
    dsimp only [R']
    rw [Function.update_of_ne hne, liveInactiveProfileBatch_at p X hG hK active s repairLiveMode w R
      repairAllSourceProfileJobs repairAllSourceProfileJobs_nodup j hj]
    exact repairAllSourceProfile_length p X hG hK active s w j hj
  have hcost (ks : List (Fin 11)) (hks : ∀ j ∈ ks, j ∈ repairAllSourceProfileJobs) :
      metadataCleanCost R' (liveInactiveProfileTargets ks) = (ks.map (fun j => 2 * ((if j = 1 ∨ j = 2 then p.wc else p.n) * (w.selectorBits + 3)) + 2)).sum + 1 := by
    induction ks with
    | nil => simp [liveInactiveProfileTargets, metadataCleanCost]
    | cons j ks ih =>
      simp only [liveInactiveProfileTargets, List.map_cons, metadataCleanCost, List.map_cons, List.sum_cons]
      have hi := ih (fun k hk => hks k (by simp [hk]))
      dsimp only [liveInactiveProfileTargets] at hi
      rw [hlen j (hks j (by simp)), hi]
      omega
  rw [hcost repairAllSourceProfileJobs (fun _ h => h)]
  simp [repairAllSourceProfileJobs, repairControlProfileJobs, repairTemporaryProfileJobs, repairYZProfileJobs, repairActivityProfileJobs,
    repairGeneratedProfileJobs, repairInactiveProfileJobs]
  omega

theorem repairAllSourceProfileClean_cost_le (R : Fin T₀ → List (Fin (A + 4)))
    (str : Fin T₀) (hstr : str ∉ liveInactiveProfileTargets repairAllSourceProfileJobs)
    (out : List (Fin (A + 4))) (n Ls : ℕ)
    (hn : p.n ≤ n) (hwc : p.wc ≤ n) (hselector : w.selectorBits ≤ Ls) :
    metadataCleanCost
      (Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w R repairAllSourceProfileJobs) str out)
      (liveInactiveProfileTargets repairAllSourceProfileJobs) ≤ 11 * (2 * (n * (Ls + 3)) + 2) + 1 := by
  rw [repairAllSourceProfileClean_cost p X hG hK active s w R str hstr out]
  have hs : w.selectorBits + 3 ≤ Ls + 3 := by omega
  have hi := Nat.mul_le_mul hn hs
  have hc := Nat.mul_le_mul hwc hs
  omega

theorem repairAllSourceProfileClean_exec (body : P → Pr P T₀ Q A U)
    (v : HS T₀ Q A U) (S : Stacks T₀ A)
    (hblank : ∀ j ∈ repairAllSourceProfileJobs, S.R (e₀ (liveDescriptorAux (.input j))) = [])
    (str : Fin T₀) (hstr : str ∉ liveInactiveProfileTargets repairAllSourceProfileJobs)
    (out : List (Fin (A + 4))) :
    let R := Function.update (liveInactiveProfileBatchBank p X hG hK active s repairLiveMode w S.R repairAllSourceProfileJobs) str out
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (liveInactiveProfileTargets repairAllSourceProfileJobs)) (mk v { S with R := R })
        (9 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 2 * (2 * (p.wc * (w.selectorBits + 3)) + 2) + 1) (mk v' { S with R := Function.update S.R str out }) := by
  obtain ⟨v', hu, hx⟩ := liveInactiveProfileClean_exec p X hG hK active s repairLiveMode w body
    repairAllSourceProfileJobs repairAllSourceProfileJobs_nodup v S hblank str hstr out
  rw [repairAllSourceProfileClean_cost p X hG hK active s w S.R str hstr out] at hx
  exact ⟨v', hu, hx⟩

end
end IntegerMultBounds.MathlibTM2.Routing
