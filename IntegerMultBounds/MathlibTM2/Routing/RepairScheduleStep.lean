module

public import IntegerMultBounds.MathlibTM2.Routing.RepairScheduleStage

/-! Discharge the uniform loop's step premise with actual framed exact repair. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K M B : ℕ} {P U : Type}

theorem repairScheduleStep_exec (stage : RepairScheduleStage K M B)
    (body : P → Pr P repairT Q (prime + K) U)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hB : 1 ≤ B)
    (delimiter : Fin (prime + K + 4)) (scan : Fin (prime + K + 4) → Bool)
    (hstop : scan delimiter = false)
    (hword : ∀ key, ∀ x ∈ stage.words (repairSetupSource key), scan x = true)
    (rest : List (Fin (prime + K + 4))) (u : HS repairT Q (prime + K) U)
    (S : Stacks repairT (prime + K)) (ready : RepairScheduleReady M B S)
    (hinput : S.R repairConfigInput = stage.frame delimiter ++ rest) :
    let C : Stacks repairT (prime + K) := { S with R := delimitedCallAdvanced S.R repairConfigInput repairConfigArchive repairHost.src (stage.frame delimiter) rest (repairStreamEffect stage.perm B (S.R repairHost.src)) }
    ∃ (u' : HS repairT Q (prime + K) U) (steps : ℕ), u'.user = u.user ∧
      (steps : ℝ) ≤ stage.stepPrice delimiter ∧ RepairScheduleReady M B C ∧
      Exec body (delimitedBankCall repairConfigInput repairConfigTmp repairConfigArchive delimiter scan
        repairConfigDestinations (repairProgram hQ hA)) (mk u S) steps (mk u' C) := by
  obtain ⟨l, hl, hrecords, hstream⟩ := ready.stream
  have hcount : l.length = stage.rows * 2 ^ fieldsLen (selectiveLen stage.p stage.X) := hl.trans stage.count.symm
  obtain ⟨u', steps, hu, hm, hx⟩ := framedExactSelective_exec stage.p stage.X stage.rb stage.hG stage.hK
    stage.guard stage.scale stage.scale_pos stage.digits_le stage.radix stage.gap stage.active stage.sources
    body hQ hA stage.rows_pos hB stage.rows_fit stage.allowed stage.words stage.data
    delimiter scan hstop hword rest u S hinput ready.tmp ready.raw ready.targets ready.left ready.blank
    l hcount hrecords hstream
  let G : Stacks repairT (prime + K) := { S with R := delimitedBankLoaded repairConfigInput repairConfigTmp repairConfigArchive delimiter rest (repairConfigLoadJobs stage.words) S.R }
  have hprice : repairRawPrice stage.p stage.X stage.rb stage.wb stage.wm stage.wp stage.wk stage.rows B stage.scale G =
      stage.price := by
    apply repairRawPrice_congr
    · intro key
      exact repairConfigLoaded_source repairConfigInput repairConfigTmp repairConfigArchive delimiter rest
        stage.words S.R (fun key => (repairRawSource_setupSource 0 key).symm)
        (fun key => (repairRawSource_setupSource 1 key).symm)
        (fun key => (repairRawSource_setupSource 2 key).symm) key
    · intro j hj
      exact (repairConfigLoader_blank delimiter rest stage.words S.R j hj).trans (ready.blank j hj)
    · exact stage.blank
  change (steps : ℝ) ≤ repairRawPrice stage.p stage.X stage.rb stage.wb stage.wm stage.wp stage.wk stage.rows B stage.scale G + _ at hm
  rw [hprice] at hm
  have hout : (moveRecs (selectiveIdealPerm stage.hK stage.active stage.sources stage.rows stage.allowed) l).flatten =
      repairStreamEffect stage.perm B (S.R repairHost.src) := by
    rw [repairStreamEffect, hstream, ← flatten_moveRecs stage.perm l (fun r hr => (hrecords r hr).1),
      RepairScheduleStage.perm, moveRecs_castRankPerm]
  rw [hout] at hx
  exact ⟨u', steps, hu, hm, RepairScheduleReady.advance S ready stage.perm (stage.frame delimiter) rest, hx⟩

end
end IntegerMultBounds.MathlibTM2.Routing
