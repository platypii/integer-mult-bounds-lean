module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedRepairScheduleStage
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankSchedule
public import IntegerMultBounds.MathlibTM2.Node.CompactProg

/-! Repeated generated/placed calls on a fixed bank, with summed costs and complete metadata rewind. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K M B : ℕ} {P P' P'' U : Type}
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "str₀" => inactiveClassifierPlacementEmbed (t₀ := t₀) (classifierCore (inactiveConfigurationCore repairHost.src))

def generatedRepairSchedulePerm : List (GeneratedRepairScheduleStage t₀ Q K M B P P' U) → Equiv.Perm (Fin M)
  | [] => Equiv.refl _
  | stage :: stages => stage.perm.trans (generatedRepairSchedulePerm stages)

theorem generatedRepairScheduleEffect_moveRecs (stages : List (GeneratedRepairScheduleStage t₀ Q K M B P P' U))
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = M)
    (hlen : ∀ r ∈ l, r.length = B) :
    delimitedScheduleEffect (fun stage => repairStreamEffect stage.perm B) stages l.flatten =
      (moveRecs (generatedRepairSchedulePerm stages) l).flatten := by
  induction stages generalizing l with
  | nil => simp only [delimitedScheduleEffect, generatedRepairSchedulePerm, moveRecs_refl l hl]
  | cons stage stages ih =>
    rw [delimitedScheduleEffect]
    have hfirst : repairStreamEffect stage.perm B l.flatten = (moveRecs stage.perm l).flatten :=
      (flatten_moveRecs stage.perm l hlen).symm
    rw [hfirst, ih (moveRecs stage.perm l) (length_moveRecs _ _)
      (fun r hr => hlen r (mem_moveRecs stage.perm hl hr))]
    exact congrArg List.flatten (moveRecs_trans stage.perm (generatedRepairSchedulePerm stages) l hl).symm

/-- Arbitrarily many actual generated/placed calls share one bank and one program.
Only pure program identities and framed input readiness are required per stage. -/
theorem framedGeneratedRepairSchedule_exec
    (outerBody : P'' → Pr P'' (TP₀ + 3) Q (prime + K) U) (ι : P' → P'')
    (program : Pr P' TP₀ Q (prime + K) U)
    (delimiter : Fin (prime + K + 4)) (scan : Fin (prime + K + 4) → Bool)
    (hstop : scan delimiter = false)
    (stages : List (GeneratedRepairScheduleStage t₀ Q K M B P P' U))
    (hbody : ∀ stage ∈ stages, ∀ f,
      outerBody (ι f) = embProg (framedCoreEmbed TP₀) ι (stage.input.placementBody f))
    (hcode : ∀ stage ∈ stages, stage.program = program)
    (hword : ∀ stage ∈ stages, ∀ j, j ≠ str₀ → ∀ x ∈ stage.input.M.R j, scan x = true)
    (v : HS (TP₀ + 3) Q (prime + K) U) (S : Stacks (TP₀ + 3) (prime + K))
    (ready : FramedCoreReady str₀ M B S)
    (hinput : S.R (framedCoreAux TP₀ 0) =
      delimitedScheduleInput (fun stage => stage.frame delimiter) stages)
    (hsaved : S.R (framedCoreAux TP₀ 2) = []) :
    ∃ (v' : HS (TP₀ + 3) Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ delimitedSchedulePrice (fun stage => stage.stepPrice delimiter) stages +
        (2 * (delimitedScheduleInput (fun stage => stage.frame delimiter) stages).length + 3 : ℕ) ∧
      Exec outerBody (delimitedScheduleProgram (framedCoreAux TP₀ 0) (framedCoreAux TP₀ 2)
        (framedCoreCallProgram str₀ delimiter scan ι program))
        (IntegerMultBounds.MathlibTM2.Host.mk v S) steps
        (IntegerMultBounds.MathlibTM2.Host.mk v' { S with R := Function.update S.R (framedCoreEmbed TP₀ str₀) (delimitedScheduleEffect (fun stage => repairStreamEffect stage.perm B) stages (S.R (framedCoreEmbed TP₀ str₀))) }) := by
  apply delimitedSchedule_exec outerBody (framedCoreAux TP₀ 0) (framedCoreAux TP₀ 2)
    (framedCoreEmbed TP₀ str₀) (framedCoreStream_nodup TP₀ str₀)
    (fun stage => stage.frame delimiter) (fun stage => repairStreamEffect stage.perm B)
    (fun stage => stage.stepPrice delimiter) (FramedCoreReady str₀ M B)
    (framedCoreCallProgram str₀ delimiter scan ι program) stages ?_ ?_ v S ready hinput hsaved
  · intro stage _
    dsimp only [GeneratedRepairScheduleStage.frame]
    apply delimitedBankFrames_ne_nil delimiter _ (framedCoreDestinations (framedCoreEmbed TP₀) str₀)
      (framedCoreJobs_destinations _ _ _)
    intro he
    have hlen := congrArg List.length he
    simp only [framedCoreDestinations, List.length_map, List.length_nil] at hlen
    have hN : 2 ≤ TP₀ := by unfold inactiveClassifierPlacementT sharedScheduleT; omega
    exact framedCoreRegisters_ne_nil str₀ hN (List.length_eq_zero_iff.mp hlen)
  · intro stage hstage rest u C hr hi
    have h := generatedRepairScheduleStep_exec stage outerBody ι (hbody stage hstage)
      delimiter scan hstop (hword stage hstage) rest u C hr hi
    rw [hcode stage hstage] at h
    exact h

end
end IntegerMultBounds.MathlibTM2.Routing
