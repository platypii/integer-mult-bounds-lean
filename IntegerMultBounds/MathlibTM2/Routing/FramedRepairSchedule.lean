module

public import IntegerMultBounds.MathlibTM2.Routing.RepairScheduleStep
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankSchedule
public import IntegerMultBounds.MathlibTM2.Node.CompactProg

/-! Repeated actual exact-repair calls on a single fixed bank, with all raw
configuration input rewound and every non-stream tape restored. Raw words are
supplied; matching-derived production and global amortization remain separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K M B : ℕ} {P U : Type}

theorem repairConfigDestinations_ne_nil : repairConfigDestinations ≠ [] := by
  intro he
  have hm : repairSetupSource (.inr .row) ∈ repairConfigDestinations :=
    List.mem_map.mpr ⟨.inr .row, repairSetupKeys_mem _, rfl⟩
  simp only [he, List.not_mem_nil] at hm

def repairSchedulePerm : List (RepairScheduleStage K M B) → Equiv.Perm (Fin M)
  | [] => Equiv.refl _
  | stage :: stages => stage.perm.trans (repairSchedulePerm stages)

theorem repairScheduleEffect_moveRecs (stages : List (RepairScheduleStage K M B))
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = M)
    (hlen : ∀ r ∈ l, r.length = B) :
    delimitedScheduleEffect (fun stage => repairStreamEffect stage.perm B) stages l.flatten =
      (moveRecs (repairSchedulePerm stages) l).flatten := by
  induction stages generalizing l with
  | nil => simp only [delimitedScheduleEffect, repairSchedulePerm, moveRecs_refl l hl]
  | cons stage stages ih =>
    rw [delimitedScheduleEffect]
    have hfirst : repairStreamEffect stage.perm B l.flatten = (moveRecs stage.perm l).flatten :=
      (flatten_moveRecs stage.perm l hlen).symm
    rw [hfirst, ih (moveRecs stage.perm l) (length_moveRecs _ _)
      (fun r hr => hlen r (mem_moveRecs stage.perm hl hr))]
    exact congrArg List.flatten (moveRecs_trans stage.perm (repairSchedulePerm stages) l hl).symm

/-- No per-stage execution or readiness callback is assumed: all stages execute
actual exact repair with their own geometry and configuration-only density price. -/
theorem framedRepairSchedule_exec (body : P → Pr P repairT Q (prime + K) U)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hB : 1 ≤ B)
    (delimiter : Fin (prime + K + 4)) (scan : Fin (prime + K + 4) → Bool)
    (hstop : scan delimiter = false) (stages : List (RepairScheduleStage K M B))
    (hword : ∀ stage ∈ stages, ∀ key, ∀ x ∈ stage.words (repairSetupSource key), scan x = true)
    (v : HS repairT Q (prime + K) U) (S : Stacks repairT (prime + K))
    (ready : RepairScheduleReady M B S)
    (hinput : S.R repairConfigInput = delimitedScheduleInput (fun stage => stage.frame delimiter) stages)
    (hsaved : S.R repairConfigArchive = []) :
    ∃ (v' : HS repairT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ delimitedSchedulePrice (fun stage => stage.stepPrice delimiter) stages +
        (2 * (delimitedScheduleInput (fun stage => stage.frame delimiter) stages).length + 3 : ℕ) ∧
      Exec body (delimitedScheduleProgram repairConfigInput repairConfigArchive
        (delimitedBankCall repairConfigInput repairConfigTmp repairConfigArchive delimiter scan
          repairConfigDestinations (repairProgram hQ hA))) (mk v S) steps
        (mk v' { S with R := Function.update S.R repairHost.src (delimitedScheduleEffect (fun stage => repairStreamEffect stage.perm B) stages (S.R repairHost.src)) }) := by
  apply delimitedSchedule_exec body repairConfigInput repairConfigArchive repairHost.src
    repairConfigLoader_stream_nodup (fun stage => stage.frame delimiter)
    (fun stage => repairStreamEffect stage.perm B) (fun stage => stage.stepPrice delimiter)
    (RepairScheduleReady M B) _ stages ?_ ?_ v S ready hinput hsaved
  · intro stage _
    exact delimitedBankFrames_ne_nil delimiter (repairConfigLoadJobs stage.words)
      repairConfigDestinations (repairConfigLoadJobs_destinations _) repairConfigDestinations_ne_nil
  · intro stage hstage rest u C hr hi
    exact repairScheduleStep_exec stage body hQ hA hB delimiter scan hstop (hword stage hstage) rest u C hr hi

end
end IntegerMultBounds.MathlibTM2.Routing
