module

public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderFrame
public import IntegerMultBounds.MathlibTM2.Routing.RepairHeaderBank

/-! Erase all ten generated headers after repair, retaining the changed stream.
The exact cleanup price depends only on the ten canonical header lengths. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

theorem repairHeaderIndex_surjective : Function.Surjective repairHeaderIndex := by
  rintro ⟨c, k⟩
  have hc := c.isLt
  have hk := k.isLt
  refine ⟨⟨5 * c.val + k.val, by omega⟩, ?_⟩
  apply Prod.ext <;> apply Fin.ext <;> dsimp [repairHeaderIndex] <;> omega

def repairGeneratedHeaderTargets : List (Fin repairHeaderT) :=
  List.ofFn (fun j : Fin 10 => repairHeaderRawCore (repairHeaderDestination j))

theorem repairGeneratedHeaderTargets_nodup : repairGeneratedHeaderTargets.Nodup :=
  List.nodup_ofFn.mpr (repairHeaderRawCore_injective.comp repairHeaderDestination_injective)

theorem repairGeneratedHeaderTargets_src : repairHeaderRawCore repairHost.src ∉ repairGeneratedHeaderTargets := by
  intro hm
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
  exact (repairSetup_source_src (.inl (.header (repairHeaderIndex j).1 (repairHeaderIndex j).2)))
    (repairHeaderRawCore_injective hj)

def repairHeaderErasePrice (p : Par) (X rb R B : ℕ) : ℕ :=
  (List.ofFn (fun j : Fin 10 => 2 * (repairCanonicalHeaders p X rb R B (repairHeaderIndex j).1 (repairHeaderIndex j).2).length + 2)).sum + 1

theorem repairHeaderErasePrice_le (p : Par) (X rb R B width : ℕ)
    (hheaders : ∀ c k, (repairCanonicalHeaders p X rb R B c k).length ≤ width) :
    repairHeaderErasePrice p X rb R B ≤ 10 * (2 * width + 2) + 1 := by
  unfold repairHeaderErasePrice
  rw [List.sum_ofFn]
  have hs : (∑ j : Fin 10,
      (2 * (repairCanonicalHeaders p X rb R B (repairHeaderIndex j).1 (repairHeaderIndex j).2).length + 2)) ≤
      ∑ _j : Fin 10, (2 * width + 2) := by
    apply Finset.sum_le_sum
    intro j _
    have hh := hheaders (repairHeaderIndex j).1 (repairHeaderIndex j).2
    omega
  simpa using Nat.add_le_add_right hs 1

theorem metadataCleanCost_eq_sum {T A : ℕ} (tapes : Fin T → List (Fin (A + 4))) (ks : List (Fin T)) :
    metadataCleanCost tapes ks = (ks.map (fun k => 2 * (tapes k).length + 2)).sum + 1 := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp only [metadataCleanCost, ih, List.map_cons, List.sum_cons]; omega

theorem repairHeadersClean_exec {Q A : ℕ} {P U : Type}
    (body : P → Pr P repairHeaderT Q A U) (p : Par) (X rb R B : ℕ)
    (v : HS repairHeaderT Q A U) (S : Stacks repairHeaderT A) (records : List (Fin (A + 4)))
    (hblank : ∀ c k, S.R (repairHeaderRawCore (repairRoutingConfig (.header c k))) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (metadataClean repairGeneratedHeaderTargets)
        (mk v { S with R := Function.update (repairHeaderPairBank p X rb R B repairSharedHeaderBank S.R) (repairHeaderRawCore repairHost.src) records }) (repairHeaderErasePrice p X rb R B)
        (mk v' { S with R := Function.update S.R (repairHeaderRawCore repairHost.src) records }) := by
  let generated := repairHeaderPairBank p X rb R B repairSharedHeaderBank S.R
  let S₁ : Stacks repairHeaderT A := { S with R := Function.update generated (repairHeaderRawCore repairHost.src) records }
  obtain ⟨v', hu, he⟩ := metadataClean_exec body repairGeneratedHeaderTargets repairGeneratedHeaderTargets_nodup v S₁
  have hc : metadataCleanCost S₁.R repairGeneratedHeaderTargets = repairHeaderErasePrice p X rb R B := by
    rw [metadataCleanCost_eq_sum]
    unfold repairGeneratedHeaderTargets repairHeaderErasePrice
    rw [List.map_ofFn]
    apply congrArg (fun f : Fin 10 → ℕ => (List.ofFn f).sum + 1)
    funext j
    have hs : repairHeaderRawCore (repairHeaderDestination j) ≠ repairHeaderRawCore repairHost.src :=
      repairHeaderRawCore_injective.ne (repairSetup_source_src (.inl (.header (repairHeaderIndex j).1 (repairHeaderIndex j).2)))
    dsimp only [Function.comp_apply, S₁]
    rw [Function.update_of_ne hs]
    dsimp only [generated, repairHeaderDestination]
    rw [repairHeaderPairBank_raw_header, List.length_map]
  have hf : metadataCleared generated repairGeneratedHeaderTargets = S.R := by
    funext i
    by_cases hi : i ∈ repairGeneratedHeaderTargets
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
      simpa only [repairHeaderDestination, hj, repairSharedHeaderBank_header, repairHeaderRawCore] using heq.symm
  have hfinal : metadataCleared S₁.R repairGeneratedHeaderTargets =
      Function.update S.R (repairHeaderRawCore repairHost.src) records := by
    rw [metadataCleared_update _ _ _ _ repairGeneratedHeaderTargets_src, hf]
  rw [hc, hfinal] at he
  exact ⟨v', hu, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
