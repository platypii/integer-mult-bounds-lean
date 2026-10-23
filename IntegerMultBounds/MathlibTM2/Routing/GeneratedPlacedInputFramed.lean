module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedInputSemantics
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreCall

/-! Actual generated/placed execution from framed input for the current record stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K : ℕ} {P P' P'' U : Type}
local notation "T₀" => liveInactiveProfileT repairT 11
local notation "e₀" => liveInactiveProfileCore (N := repairT) (J := 11)
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "ep₀" => inactiveClassifierPlacementEmbed (t₀ := t₀)
local notation "slot₀" => inactiveClassifierPlacementSlot (t₀ := t₀)

local notation "str₀" => ep₀ (classifierCore (inactiveConfigurationCore repairHost.src))

/-- A real generated/placed call from framed metadata, for the current stream. -/
theorem GeneratedPlacedInput.framed_exec (input : GeneratedPlacedInput t₀ Q K P P' U)
    (outerBody : P'' → Pr P'' (TP₀ + 3) Q (prime + K) U) (ι : P' → P'')
    (hbody : ∀ f, outerBody (ι f) = embProg (framedCoreEmbed TP₀) ι (input.placementBody f))
    (delimiter : Fin (prime + K + 4)) (scan : Fin (prime + K + 4) → Bool)
    (hstop : scan delimiter = false)
    (hword : ∀ j, j ≠ str₀ → ∀ x ∈ input.M.R j, scan x = true)
    (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = input.R * 2 ^ fieldsLen (selectiveLen input.p input.X))
    (hlen : ∀ r ∈ l, r.length = input.B ∧ ∀ a ∈ r, a.val < 8)
    (rest : List (Fin (prime + K + 4)))
    (v : HS (TP₀ + 3) Q (prime + K) U) (S : Stacks (TP₀ + 3) (prime + K))
    (hinput : S.R (framedCoreAux TP₀ 0) =
      delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed TP₀) str₀ input.M.R) ++ rest)
    (htmp : S.R (framedCoreAux TP₀ 1) = [])
    (hblank : ∀ j, j ≠ str₀ → S.R (framedCoreEmbed TP₀ j) = [])
    (hleft : ∀ j, S.L (framedCoreEmbed TP₀ j) = [])
    (hstream : S.R (framedCoreEmbed TP₀ str₀) = l.flatten) :
    ∃ (v' : HS (TP₀ + 3) Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ input.price +
        (6 * (delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed TP₀) str₀ input.M.R)).length +
          2 * (framedCoreJobs (framedCoreEmbed TP₀) str₀ input.M.R).length + 2 : ℕ) ∧
      Exec outerBody (framedCoreCallProgram str₀ delimiter scan ι
        (allSourcePlacedFixedProgram input.keySrc input.raw input.activity input.hQ input.hA
          input.hd input.pay input.hhd input.hQplacement input.hT input.ι))
        (IntegerMultBounds.MathlibTM2.Host.mk v S) steps
        (IntegerMultBounds.MathlibTM2.Host.mk v' { S with R := delimitedCallAdvanced S.R (framedCoreAux TP₀ 0) (framedCoreAux TP₀ 2) (framedCoreEmbed TP₀ str₀) (delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed TP₀) str₀ input.M.R)) rest (moveRecs input.perm l).flatten }) := by
  apply framedCoreCall_exec input.placementBody outerBody ι hbody str₀ delimiter scan hstop input.M.R
    hword rest (moveRecs input.perm l).flatten v S hinput htmp hblank
    (allSourcePlacedFixedProgram input.keySrc input.raw input.activity input.hQ input.hA
      input.hd input.pay input.hhd input.hQplacement input.hT input.ι) input.price
  intro u
  apply input.exec_on l hl hlen
  · exact hleft
  · rw [hstream]

end
end IntegerMultBounds.MathlibTM2.Routing
