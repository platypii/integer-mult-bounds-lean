module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingPlacedCurrent
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreCall

/-! Load matching-table/scalar metadata, execute actual matching-derived repair,
and erase the loaded bank on three shared loader tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K : ℕ} {P P' P'' P''' U : Type}
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "N₀" => TP₀ + 36
local notation "str₀" => inactiveClassifierPlacementEmbed (t₀ := t₀) (classifierCore (inactiveConfigurationCore repairHost.src))
local notation "str₁" => matchingCoreEmbed TP₀ str₀

theorem matchingPlacedFramed_exec (input : GeneratedPlacedInput t₀ Q K P P' U)
    (ι₀ : P' → P'') (coreBody : P'' → Pr P'' N₀ Q (prime + K) U)
    (hcoreBody : ∀ f, coreBody (ι₀ f) = embProg (matchingCoreEmbed TP₀) ι₀ (input.placementBody f))
    (ι : P'' → P''') (outerBody : P''' → Pr P''' (N₀ + 3) Q (prime + K) U)
    (hbody : ∀ f, outerBody (ι f) = embProg (framedCoreEmbed N₀) ι (coreBody f))
    (hρ : input.p.ρ < input.p.K) (hinv : Function.Involutive input.source) (reverse : Bool)
    (htargets : input.targets = matchingDirectionTargets input.source reverse)
    (hwidth : input.p.wy < 2 ^ (input.w.indexBits + input.w.strideBits)) (Lc : ℕ)
    (hcountFit : (input.p.n * input.p.K) * (2 * (input.w.indexBits + input.w.strideBits) + 2) < 2 ^ Lc)
    (delimiter : Fin (prime + K + 4)) (scan : Fin (prime + K + 4) → Bool)
    (hstop : scan delimiter = false)
    (hword : ∀ j, j ≠ str₁ → ∀ x ∈ matchingPlacedInputBank input Lc j, scan x = true)
    (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = input.R * 2 ^ fieldsLen (selectiveLen input.p input.X))
    (hlen : ∀ r ∈ l, r.length = input.B ∧ ∀ a ∈ r, a.val < 8)
    (rest : List (Fin (prime + K + 4)))
    (v : HS (N₀ + 3) Q (prime + K) U) (S : Stacks (N₀ + 3) (prime + K))
    (hinput : S.R (framedCoreAux N₀ 0) =
      delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed N₀) str₁ (matchingPlacedInputBank input Lc)) ++ rest)
    (htmp : S.R (framedCoreAux N₀ 1) = [])
    (hblank : ∀ j, j ≠ str₁ → S.R (framedCoreEmbed N₀ j) = [])
    (hleft : ∀ j, S.L (framedCoreEmbed N₀ j) = [])
    (hstream : S.R (framedCoreEmbed N₀ str₁) = l.flatten) :
    ∃ (v' : HS (N₀ + 3) Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ matchingPlacedRepairPrice input Lc +
        (6 * (delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed N₀) str₁ (matchingPlacedInputBank input Lc))).length +
          2 * (framedCoreJobs (framedCoreEmbed N₀) str₁ (matchingPlacedInputBank input Lc)).length + 2 : ℕ) ∧
      Exec outerBody (framedCoreCallProgram str₁ delimiter scan ι (matchingGeneratedPlacedProgram input
        (matchingCoreEmbed TP₀) ι₀ (matchingExtractSlot TP₀) (matchingGatherSlot TP₀) (matchingGenerateSlot TP₀) reverse))
        (mk v S) steps
        (mk v' { S with R := delimitedCallAdvanced S.R (framedCoreAux N₀ 0) (framedCoreAux N₀ 2) (framedCoreEmbed N₀ str₁) (delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed N₀) str₁ (matchingPlacedInputBank input Lc))) rest (moveRecs input.perm l).flatten }) := by
  apply framedCoreCall_exec coreBody outerBody ι hbody str₁ delimiter scan hstop (matchingPlacedInputBank input Lc)
    hword rest (moveRecs input.perm l).flatten v S hinput htmp hblank
    (matchingGeneratedPlacedProgram input (matchingCoreEmbed TP₀) ι₀ (matchingExtractSlot TP₀)
      (matchingGatherSlot TP₀) (matchingGenerateSlot TP₀) reverse) (matchingPlacedRepairPrice input Lc)
  intro u
  apply matchingFixedPlacedRepair_on input ι₀ coreBody hcoreBody hρ hinv reverse htargets hwidth Lc
    hcountFit l hl hlen u
  · rw [hstream]
  · intro j
    exact hleft (matchingCoreEmbed TP₀ j)

end
end IntegerMultBounds.MathlibTM2.Routing
