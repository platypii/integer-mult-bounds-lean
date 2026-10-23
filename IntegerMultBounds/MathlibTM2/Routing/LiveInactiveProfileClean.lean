module

public import IntegerMultBounds.MathlibTM2.Routing.LiveInactiveProfileBatch
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Erase generated inactive profiles after a disjoint stream update.
Cleanup restores the entire initial bank except that changed stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {N J Q A : ℕ} {P U : Type}
variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
  (mode : Fin J → LiveDescriptorMode) (w : LiveDescriptorWidths)

def liveInactiveProfileTargets (jobs : List (Fin J)) : List (Fin (liveInactiveProfileT N J)) :=
  jobs.map (fun j => liveInactiveProfileCore (liveDescriptorAux (.input j)))

theorem liveInactiveProfileTargets_nodup (jobs : List (Fin J)) (hnd : jobs.Nodup) :
    (liveInactiveProfileTargets (N := N) jobs).Nodup :=
  hnd.map (liveInactiveProfileCore_injective.comp (liveDescriptorAux_injective.comp
    (by intro i j h; cases h; rfl)))

theorem liveInactiveProfileClean_restore
    (R : Fin (liveInactiveProfileT N J) → List (Fin (A + 4))) (jobs : List (Fin J))
    (hblank : ∀ j ∈ jobs, R (liveInactiveProfileCore (liveDescriptorAux (.input j))) = []) :
    metadataCleared (liveInactiveProfileBatchBank p X hG hK active s mode w R jobs)
      (liveInactiveProfileTargets jobs) = R := by
  funext i
  by_cases hi : i ∈ liveInactiveProfileTargets jobs
  · rw [metadataCleared_at _ _ _ hi]
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact (hblank j hj).symm
  · rw [metadataCleared_keep _ _ _ hi]
    apply liveInactiveProfileBatch_keep
    intro j hj he
    exact hi (List.mem_map.mpr ⟨j, hj, he.symm⟩)

theorem liveInactiveProfileClean_cost
    (R : Fin (liveInactiveProfileT N J) → List (Fin (A + 4))) (jobs : List (Fin J)) (hnd : jobs.Nodup)
    (hprofiles : ∀ j ∈ jobs, (mode j).profileFrames (A := A) p X hG hK active s w.selectorBits =
      affineProfileFrames w.selectorBits (List.replicate p.n (false, 0)))
    (str : Fin (liveInactiveProfileT N J)) (hstr : str ∉ liveInactiveProfileTargets jobs)
    (out : List (Fin (A + 4))) :
    metadataCleanCost
      (Function.update (liveInactiveProfileBatchBank p X hG hK active s mode w R jobs) str out)
      (liveInactiveProfileTargets jobs) = jobs.length * (2 * (p.n * (w.selectorBits + 3)) + 2) + 1 := by
  let R' := Function.update (liveInactiveProfileBatchBank p X hG hK active s mode w R jobs) str out
  have hlen (j : Fin J) (hj : j ∈ jobs) :
      (R' (liveInactiveProfileCore (liveDescriptorAux (.input j)))).length = p.n * (w.selectorBits + 3) := by
    have hne : liveInactiveProfileCore (liveDescriptorAux (.input j)) ≠ str := by
      intro he
      exact hstr (List.mem_map.mpr ⟨j, hj, he⟩)
    dsimp only [R']
    rw [Function.update_of_ne hne, liveInactiveProfileBatch_at p X hG hK active s mode w R jobs hnd j hj,
      hprofiles j hj, affineProfileFrames_length, List.length_replicate]
  have hcost (ks : List (Fin J)) (hks : ∀ j ∈ ks, j ∈ jobs) :
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
  exact hcost jobs (fun _ h => h)

theorem liveInactiveProfileClean_exec (body : P → Pr P (liveInactiveProfileT N J) Q A U)
    (jobs : List (Fin J)) (hnd : jobs.Nodup)
    (v : HS (liveInactiveProfileT N J) Q A U) (S : Stacks (liveInactiveProfileT N J) A)
    (hblank : ∀ j ∈ jobs, S.R (liveInactiveProfileCore (liveDescriptorAux (.input j))) = [])
    (str : Fin (liveInactiveProfileT N J)) (hstr : str ∉ liveInactiveProfileTargets jobs)
    (out : List (Fin (A + 4))) :
    let R := Function.update (liveInactiveProfileBatchBank p X hG hK active s mode w S.R jobs) str out
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (liveInactiveProfileTargets jobs))
        (mk v { S with R := R }) (metadataCleanCost R (liveInactiveProfileTargets jobs))
        (mk v' { S with R := Function.update S.R str out }) := by
  dsimp only
  obtain ⟨v', hu, hx⟩ := metadataClean_exec body (liveInactiveProfileTargets jobs)
    (liveInactiveProfileTargets_nodup jobs hnd) v
    { S with R := Function.update (liveInactiveProfileBatchBank p X hG hK active s mode w S.R jobs) str out }
  rw [metadataCleared_update _ _ str out hstr, liveInactiveProfileClean_restore p X hG hK active s mode w S.R jobs hblank] at hx
  exact ⟨v', hu, hx⟩

end
end IntegerMultBounds.MathlibTM2.Routing
