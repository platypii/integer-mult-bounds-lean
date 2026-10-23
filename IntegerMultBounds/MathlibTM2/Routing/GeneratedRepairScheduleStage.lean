module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedInputFramed
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreReady
public import IntegerMultBounds.MathlibTM2.Routing.RepairScheduleStage

/-! A concrete generated/placed stage on a common fixed-size record stream. -/

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

structure GeneratedRepairScheduleStage (t₀ Q K M B : ℕ) (P P' U : Type) where
  input : GeneratedPlacedInput t₀ Q K P P' U
  count : input.R * 2 ^ fieldsLen (selectiveLen input.p input.X) = M
  width : input.B = B

def GeneratedRepairScheduleStage.perm (stage : GeneratedRepairScheduleStage t₀ Q K M B P P' U) :
    Equiv.Perm (Fin M) := castRankPerm stage.count stage.input.perm

def GeneratedRepairScheduleStage.program (stage : GeneratedRepairScheduleStage t₀ Q K M B P P' U) :
    Pr P' TP₀ Q (prime + K) U :=
  allSourcePlacedFixedProgram stage.input.keySrc stage.input.raw stage.input.activity stage.input.hQ
    stage.input.hA stage.input.hd stage.input.pay stage.input.hhd stage.input.hQplacement stage.input.hT stage.input.ι

def GeneratedRepairScheduleStage.frame (stage : GeneratedRepairScheduleStage t₀ Q K M B P P' U)
    (delimiter : Fin (prime + K + 4)) :=
  delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed TP₀) str₀ stage.input.M.R)

def GeneratedRepairScheduleStage.stepPrice (stage : GeneratedRepairScheduleStage t₀ Q K M B P P' U)
    (delimiter : Fin (prime + K + 4)) : ℝ :=
  stage.input.price + (6 * (stage.frame delimiter).length +
    2 * (framedCoreJobs (framedCoreEmbed TP₀) str₀ stage.input.M.R).length + 2 : ℕ)

/-- Every step runs the actual generated pipeline; no execution callback is supplied. -/
theorem generatedRepairScheduleStep_exec (stage : GeneratedRepairScheduleStage t₀ Q K M B P P' U)
    (outerBody : P'' → Pr P'' (TP₀ + 3) Q (prime + K) U) (ι : P' → P'')
    (hbody : ∀ f, outerBody (ι f) = embProg (framedCoreEmbed TP₀) ι (stage.input.placementBody f))
    (delimiter : Fin (prime + K + 4)) (scan : Fin (prime + K + 4) → Bool)
    (hstop : scan delimiter = false)
    (hword : ∀ j, j ≠ str₀ → ∀ x ∈ stage.input.M.R j, scan x = true)
    (rest : List (Fin (prime + K + 4))) (u : HS (TP₀ + 3) Q (prime + K) U)
    (S : Stacks (TP₀ + 3) (prime + K)) (ready : FramedCoreReady str₀ M B S)
    (hinput : S.R (framedCoreAux TP₀ 0) = stage.frame delimiter ++ rest) :
    let C : Stacks (TP₀ + 3) (prime + K) := { S with R := delimitedCallAdvanced S.R (framedCoreAux TP₀ 0) (framedCoreAux TP₀ 2) (framedCoreEmbed TP₀ str₀) (stage.frame delimiter) rest (repairStreamEffect stage.perm B (S.R (framedCoreEmbed TP₀ str₀))) }
    ∃ (u' : HS (TP₀ + 3) Q (prime + K) U) (steps : ℕ), u'.user = u.user ∧
      (steps : ℝ) ≤ stage.stepPrice delimiter ∧ FramedCoreReady str₀ M B C ∧
      Exec outerBody (framedCoreCallProgram str₀ delimiter scan ι stage.program)
        (IntegerMultBounds.MathlibTM2.Host.mk u S) steps (IntegerMultBounds.MathlibTM2.Host.mk u' C) := by
  obtain ⟨l, hl, hrecords, hstream⟩ := ready.stream
  have hcount := hl.trans stage.count.symm
  have hshape : ∀ r ∈ l, r.length = stage.input.B ∧ ∀ a ∈ r, a.val < 8 := by
    simpa only [stage.width] using hrecords
  obtain ⟨u', steps, hu, hm, he⟩ := stage.input.framed_exec outerBody ι hbody delimiter scan hstop
    hword l hcount hshape rest u S hinput ready.tmp ready.blank ready.left hstream
  have hout : (moveRecs stage.input.perm l).flatten =
      repairStreamEffect stage.perm B (S.R (framedCoreEmbed TP₀ str₀)) := by
    rw [repairStreamEffect, hstream, ← flatten_moveRecs stage.perm l (fun r hr => (hrecords r hr).1),
      GeneratedRepairScheduleStage.perm, moveRecs_castRankPerm]
  rw [hout] at he
  exact ⟨u', steps, hu, hm, FramedCoreReady.advance str₀ S ready stage.perm (stage.frame delimiter) rest, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
