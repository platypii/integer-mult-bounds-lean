module

public import IntegerMultBounds.MathlibTM2.Routing.EmbeddedRepairHeaderData
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeadersClean
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderBank

/-! Erase all ten generated headers after repair, retaining the changed stream.
The exact cleanup price depends only on the ten canonical header lengths. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {N : ℕ} (e : Fin repairT → Fin N) (he : Function.Injective e)

def embeddedGeneratedHeaderTargets : List (Fin (sharedHeaderT N)) :=
  List.ofFn (fun j : Fin 10 => embeddedRepairHeaderRaw e (repairHeaderDestination j))

include he

theorem embeddedGeneratedHeaderTargets_nodup : (embeddedGeneratedHeaderTargets e).Nodup :=
  List.nodup_ofFn.mpr ((embeddedRepairHeaderRaw_injective e he).comp repairHeaderDestination_injective)

theorem embeddedGeneratedHeaderTargets_src : embeddedRepairHeaderRaw e repairHost.src ∉ embeddedGeneratedHeaderTargets e := by
  intro hm
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
  exact (repairSetup_source_src (.inl (.header (repairHeaderIndex j).1 (repairHeaderIndex j).2)))
    (embeddedRepairHeaderRaw_injective e he hj)

theorem embeddedRepairHeadersClean_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P (sharedHeaderT N) Q A U) (p : Par) (X rb R B : ℕ)
    (v : HS (sharedHeaderT N) Q A U) (S : Stacks (sharedHeaderT N) A) (records : List (Fin (A + 4)))
    (hblank : ∀ c k, S.R (embeddedRepairHeaderRaw e (repairRoutingConfig (.header c k))) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean (embeddedGeneratedHeaderTargets e))
        (mk v { S with R := Function.update (repairHeaderPairBank p X rb R B (embeddedRepairHeaderBank e) S.R) (embeddedRepairHeaderRaw e repairHost.src) records }) (repairHeaderErasePrice p X rb R B)
        (mk v' { S with R := Function.update S.R (embeddedRepairHeaderRaw e repairHost.src) records }) := by
  let generated := repairHeaderPairBank p X rb R B (embeddedRepairHeaderBank e) S.R
  let S₁ : Stacks (sharedHeaderT N) A := { S with R := Function.update generated (embeddedRepairHeaderRaw e repairHost.src) records }
  obtain ⟨v', hu, hex⟩ := metadataClean_exec body (embeddedGeneratedHeaderTargets e) (embeddedGeneratedHeaderTargets_nodup e he) v S₁
  have hc : metadataCleanCost S₁.R (embeddedGeneratedHeaderTargets e) = repairHeaderErasePrice p X rb R B := by
    rw [metadataCleanCost_eq_sum]
    unfold embeddedGeneratedHeaderTargets repairHeaderErasePrice
    rw [List.map_ofFn]
    apply congrArg (fun f : Fin 10 → ℕ => (List.ofFn f).sum + 1)
    funext j
    have hs : embeddedRepairHeaderRaw e (repairHeaderDestination j) ≠ embeddedRepairHeaderRaw e repairHost.src :=
      (embeddedRepairHeaderRaw_injective e he).ne (repairSetup_source_src (.inl (.header (repairHeaderIndex j).1 (repairHeaderIndex j).2)))
    dsimp only [Function.comp_apply, S₁]
    rw [Function.update_of_ne hs]
    dsimp only [generated, repairHeaderDestination]
    rw [embeddedRepairHeaderPair_raw_header e he, List.length_map]
  have hf : metadataCleared generated (embeddedGeneratedHeaderTargets e) = S.R := by
    funext i
    by_cases hi : i ∈ embeddedGeneratedHeaderTargets e
    · rw [metadataCleared_at _ _ i hi]
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
      exact (hblank (repairHeaderIndex j).1 (repairHeaderIndex j).2).symm
    · rw [metadataCleared_keep _ _ i hi]
      apply repairHeaderPairBank_keep
      intro c k heq
      obtain ⟨j, hj⟩ := repairHeaderIndex_surjective (c, k)
      apply hi
      apply List.mem_ofFn.mpr
      refine ⟨j, ?_⟩
      simpa only [repairHeaderDestination, hj, embeddedRepairHeaderBank_header, embeddedRepairHeaderRaw] using heq.symm
  have hfinal : metadataCleared S₁.R (embeddedGeneratedHeaderTargets e) =
      Function.update S.R (embeddedRepairHeaderRaw e repairHost.src) records := by
    rw [metadataCleared_update _ _ _ _ (embeddedGeneratedHeaderTargets_src e he), hf]
  rw [hc, hfinal] at hex
  exact ⟨v', hu, hex⟩

end
end IntegerMultBounds.MathlibTM2.Routing
