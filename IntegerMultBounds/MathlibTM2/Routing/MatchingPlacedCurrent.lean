module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingPlacedFrame

/-! Run a fixed matching-produced call on the current record stream, retaining
its original program and complete stage price. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K : ℕ} {P P' P'' U : Type}
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "str₀" => inactiveClassifierPlacementEmbed (t₀ := t₀) (classifierCore (inactiveConfigurationCore repairHost.src))

theorem matchingFixedPlacedRepair_on (input : GeneratedPlacedInput t₀ Q K P P' U)
    (ι : P' → P'') (body : P'' → Pr P'' (TP₀ + 36) Q (prime + K) U)
    (hbody : ∀ f, body (ι f) = embProg (matchingCoreEmbed TP₀) ι (input.placementBody f))
    (hρ : input.p.ρ < input.p.K) (hinv : Function.Involutive input.source) (reverse : Bool)
    (htargets : input.targets = matchingDirectionTargets input.source reverse)
    (hwidth : input.p.wy < 2 ^ (input.w.indexBits + input.w.strideBits)) (Lc : ℕ)
    (hcountFit : (input.p.n * input.p.K) * (2 * (input.w.indexBits + input.w.strideBits) + 2) < 2 ^ Lc)
    (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = input.R * 2 ^ fieldsLen (selectiveLen input.p input.X))
    (hlen : ∀ r ∈ l, r.length = input.B ∧ ∀ a ∈ r, a.val < 8)
    (v : HS (TP₀ + 36) Q (prime + K) U) (S : Stacks (TP₀ + 36) (prime + K))
    (hR : S.R = Function.update (matchingPlacedInputBank input Lc) (matchingCoreEmbed TP₀ str₀) l.flatten)
    (hleft : ∀ j, S.L (matchingCoreEmbed TP₀ j) = []) :
    ∃ (v' : HS (TP₀ + 36) Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ matchingPlacedRepairPrice input Lc ∧
      Exec body (matchingGeneratedPlacedProgram input (matchingCoreEmbed TP₀) ι (matchingExtractSlot TP₀)
        (matchingGatherSlot TP₀) (matchingGenerateSlot TP₀) reverse) (mk v S) steps
        (mk v' { S with R := Function.update S.R (matchingCoreEmbed TP₀ str₀) (moveRecs input.perm l).flatten }) := by
  have hbank : S.R = matchingPlacedInputBank (input.replaceRecords l hl hlen) Lc := by
    rw [input.replaceRecords_matchingBank l hl hlen]
    exact hR
  obtain ⟨v', steps, hu, hm, he⟩ := matchingFixedPlacedRepair_exec (input.replaceRecords l hl hlen)
    ι body hbody hρ hinv reverse htargets hwidth Lc hcountFit v S hbank hleft
  rw [input.replaceRecords_matchingPrice l hl hlen] at hm
  rw [input.replaceRecords_matchingProgram l hl hlen] at he
  refine ⟨v', steps, hu, hm, ?_⟩
  simpa only [GeneratedPlacedInput.replaceRecords, GeneratedPlacedInput.perm] using he

end
end IntegerMultBounds.MathlibTM2.Routing
