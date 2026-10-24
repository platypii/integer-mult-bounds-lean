module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingFixedSetup
public import IntegerMultBounds.MathlibTM2.Routing.MatchingGeneratedPlacedRepair

/-! A fixed production bank supplies the actual generated/placed repair call.
All production readiness is derived from four external inputs and blank scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K : ℕ} {P P' P'' U : Type}
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "str₀" => inactiveClassifierPlacementEmbed (t₀ := t₀) (classifierCore (inactiveConfigurationCore repairHost.src))

def matchingPlacedRepairPrice (input : GeneratedPlacedInput t₀ Q K P P' U) (Lc : ℕ) : ℝ :=
  (matchingFullProfileProductionCost input.p (input.w.indexBits + input.w.strideBits) input.w.strideBits Lc : ℕ) +
    input.price + (2 * input.coordinateWords.length + 2 : ℕ)

theorem matchingFixedPlacedRepair_exec (input : GeneratedPlacedInput t₀ Q K P P' U)
    (ι : P' → P'') (body : P'' → Pr P'' (TP₀ + 36) Q (prime + K) U)
    (hbody : ∀ f, body (ι f) = embProg (matchingCoreEmbed TP₀) ι (input.placementBody f))
    (hρ : input.p.ρ < input.p.K) (hinv : Function.Involutive input.source) (reverse : Bool)
    (htargets : input.targets = matchingDirectionTargets input.source reverse)
    (hwidth : input.p.wy < 2 ^ (input.w.indexBits + input.w.strideBits)) (Lc : ℕ)
    (hcountFit : (input.p.n * input.p.K) * (2 * (input.w.indexBits + input.w.strideBits) + 2) < 2 ^ Lc)
    (v : HS (TP₀ + 36) Q (prime + K) U) (S : Stacks (TP₀ + 36) (prime + K))
    (hR : S.R = matchingInitialBank (Function.update input.M.R input.coordinateRegister [])
      input.p input.source input.w.indexBits input.w.strideBits Lc)
    (hleft : ∀ j, S.L (matchingCoreEmbed TP₀ j) = []) :
    ∃ (v' : HS (TP₀ + 36) Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ matchingPlacedRepairPrice input Lc ∧
      Exec body (matchingGeneratedPlacedProgram input (matchingCoreEmbed TP₀) ι (matchingExtractSlot TP₀)
        (matchingGatherSlot TP₀) (matchingGenerateSlot TP₀) reverse) (mk v S) steps
        (mk v' { S with R := Function.update S.R (matchingCoreEmbed TP₀ str₀) (moveRecs input.perm input.l).flatten }) := by
  let setup := matchingFixedSetup input.p input.source input.hK hρ hinv reverse input.w.indexBits input.w.strideBits Lc
    hwidth input.hkfit hcountFit (Function.update input.M.R input.coordinateRegister []) input.coordinateRegister S hR
  have hbank : (embStk (matchingCoreEmbed TP₀) S).R = Function.update input.M.R input.coordinateRegister [] := by
    funext j
    change S.R (matchingCoreEmbed TP₀ j) = _
    rw [hR]
    exact matchingProductionBank_core _ _ _ _ _ j
  have ht : input.targets = matchingDirectionTargets input.source setup.reverse := by
    dsimp only [setup, matchingFixedSetup, matchingFixedFrame]
    exact htargets
  have h := matchingGeneratedPlacedRepair_exec input (matchingCoreEmbed TP₀) (matchingCoreEmbed_injective TP₀)
    ι body hbody Lc v S setup ht hbank hleft
  simpa only [setup, matchingFixedSetup, matchingFixedFrame, matchingPlacedRepairPrice] using h

end
end IntegerMultBounds.MathlibTM2.Routing
