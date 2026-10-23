module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingPlacedFramed
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
variable {t₀ Q K M B : ℕ} {P P' P'' P''' U : Type}
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "rawStr₀" => inactiveClassifierPlacementEmbed (t₀ := t₀) (classifierCore (inactiveConfigurationCore repairHost.src))

local notation "N₀" => TP₀ + 36
local notation "str₀" => matchingCoreEmbed TP₀ rawStr₀

structure MatchingRepairScheduleStage (t₀ Q K M B : ℕ) (P P' U : Type) where
  input : GeneratedPlacedInput t₀ Q K P P' U
  count : input.R * 2 ^ fieldsLen (selectiveLen input.p input.X) = M
  width : input.B = B
  Lc : ℕ
  hρ : input.p.ρ < input.p.K
  hinv : Function.Involutive input.source
  reverse : Bool
  htargets : input.targets = matchingDirectionTargets input.source reverse
  hwidth : input.p.wy < 2 ^ (input.w.indexBits + input.w.strideBits)
  hcountFit : (input.p.n * input.p.K) * (2 * (input.w.indexBits + input.w.strideBits) + 2) < 2 ^ Lc

def MatchingRepairScheduleStage.perm (stage : MatchingRepairScheduleStage t₀ Q K M B P P' U) :
    Equiv.Perm (Fin M) := castRankPerm stage.count stage.input.perm

def MatchingRepairScheduleStage.program (stage : MatchingRepairScheduleStage t₀ Q K M B P P' U) (ι₀ : P' → P'') :
    Pr P'' N₀ Q (prime + K) U :=
  matchingGeneratedPlacedProgram stage.input (matchingCoreEmbed TP₀) ι₀ (matchingExtractSlot TP₀)
    (matchingGatherSlot TP₀) (matchingGenerateSlot TP₀) stage.reverse

def MatchingRepairScheduleStage.frame (stage : MatchingRepairScheduleStage t₀ Q K M B P P' U)
    (delimiter : Fin (prime + K + 4)) :=
  delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed N₀) str₀ (matchingPlacedInputBank stage.input stage.Lc))

def MatchingRepairScheduleStage.stepPrice (stage : MatchingRepairScheduleStage t₀ Q K M B P P' U)
    (delimiter : Fin (prime + K + 4)) : ℝ :=
  matchingPlacedRepairPrice stage.input stage.Lc + (6 * (stage.frame delimiter).length +
    2 * (framedCoreJobs (framedCoreEmbed N₀) str₀ (matchingPlacedInputBank stage.input stage.Lc)).length + 2 : ℕ)

/-- Every step runs the actual generated pipeline; no execution callback is supplied. -/
theorem matchingRepairScheduleStep_exec (stage : MatchingRepairScheduleStage t₀ Q K M B P P' U)
    (ι₀ : P' → P'') (coreBody : P'' → Pr P'' N₀ Q (prime + K) U)
    (hcoreBody : ∀ f, coreBody (ι₀ f) = embProg (matchingCoreEmbed TP₀) ι₀ (stage.input.placementBody f))
    (outerBody : P''' → Pr P''' (N₀ + 3) Q (prime + K) U) (ι : P'' → P''')
    (hbody : ∀ f, outerBody (ι f) = embProg (framedCoreEmbed N₀) ι (coreBody f))
    (delimiter : Fin (prime + K + 4)) (scan : Fin (prime + K + 4) → Bool)
    (hstop : scan delimiter = false)
    (hword : ∀ j, j ≠ str₀ → ∀ x ∈ matchingPlacedInputBank stage.input stage.Lc j, scan x = true)
    (rest : List (Fin (prime + K + 4))) (u : HS (N₀ + 3) Q (prime + K) U)
    (S : Stacks (N₀ + 3) (prime + K)) (ready : FramedCoreReady str₀ M B S)
    (hinput : S.R (framedCoreAux N₀ 0) = stage.frame delimiter ++ rest) :
    let C : Stacks (N₀ + 3) (prime + K) := { S with R := delimitedCallAdvanced S.R (framedCoreAux N₀ 0) (framedCoreAux N₀ 2) (framedCoreEmbed N₀ str₀) (stage.frame delimiter) rest (repairStreamEffect stage.perm B (S.R (framedCoreEmbed N₀ str₀))) }
    ∃ (u' : HS (N₀ + 3) Q (prime + K) U) (steps : ℕ), u'.user = u.user ∧
      (steps : ℝ) ≤ stage.stepPrice delimiter ∧ FramedCoreReady str₀ M B C ∧
      Exec outerBody (framedCoreCallProgram str₀ delimiter scan ι (stage.program ι₀))
        (IntegerMultBounds.MathlibTM2.Host.mk u S) steps (IntegerMultBounds.MathlibTM2.Host.mk u' C) := by
  obtain ⟨l, hl, hrecords, hstream⟩ := ready.stream
  have hcount := hl.trans stage.count.symm
  have hshape : ∀ r ∈ l, r.length = stage.input.B ∧ ∀ a ∈ r, a.val < 8 := by
    simpa only [stage.width] using hrecords
  obtain ⟨u', steps, hu, hm, he⟩ := matchingPlacedFramed_exec stage.input ι₀ coreBody hcoreBody
    ι outerBody hbody stage.hρ stage.hinv stage.reverse stage.htargets stage.hwidth stage.Lc stage.hcountFit
    delimiter scan hstop hword l hcount hshape rest u S hinput ready.tmp ready.blank ready.left hstream
  have hout : (moveRecs stage.input.perm l).flatten =
      repairStreamEffect stage.perm B (S.R (framedCoreEmbed N₀ str₀)) := by
    rw [repairStreamEffect, hstream, ← flatten_moveRecs stage.perm l (fun r hr => (hrecords r hr).1),
      MatchingRepairScheduleStage.perm, moveRecs_castRankPerm]
  rw [hout] at he
  exact ⟨u', steps, hu, hm, FramedCoreReady.advance str₀ S ready stage.perm (stage.frame delimiter) rest, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
