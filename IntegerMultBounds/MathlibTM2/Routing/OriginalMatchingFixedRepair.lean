module

public import IntegerMultBounds.MathlibTM2.Routing.OriginalMatchingPlacedRepair
public import IntegerMultBounds.MathlibTM2.Routing.OriginalMatchingRepairBank

/-! The original-matching repair bridge on its concrete shared-table layout.
A single declared bank establishes both producer and repair readiness. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K : ℕ} {P P' P'' P''' U : Type}
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "N₀" => TP₀ + 36
local notation "str₀" => inactiveClassifierPlacementEmbed (t₀ := t₀) (classifierCore (inactiveConfigurationCore repairHost.src))

theorem originalMatchingFixedRepair_exec (input : GeneratedPlacedInput t₀ Q K P P' U)
    (ι₀ : P' → P'') (coreBody : P'' → Pr P'' N₀ Q (prime + K) U)
    (hcore : ∀ f, coreBody (ι₀ f) = embProg (matchingCoreEmbed TP₀) ι₀ (input.placementBody f))
    (ι : P'' → P''') (body : P''' → Pr P''' (N₀ + 57) Q (prime + K) U)
    (hbody : ∀ f, body (ι f) = embProg (originalMatchingRepairEmbed TP₀) ι (coreBody f))
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hn : n < 2 ^ (input.w.indexBits + input.w.strideBits))
    (hsize : input.p.wy = n - 3 * w)
    (hsource : input.source = fun q => Fin.cast hsize.symm
      (reservoirClassLocalMatching n H hfit w hw k mate hinv (Fin.cast hsize q)))
    (hρ : input.p.ρ < input.p.K) (reverse : Bool)
    (htargets : input.targets = matchingDirectionTargets input.source reverse) (Lc : ℕ)
    (hcountFit : (input.p.n * input.p.K) * (2 * (input.w.indexBits + input.w.strideBits) + 2) < 2 ^ Lc)
    (v : HS (N₀ + 57) Q (prime + K) U) (S : Stacks (N₀ + 57) (prime + K))
    (hbank : S.R = originalMatchingInputBank TP₀
      (matchingInitialBank (Function.update input.M.R input.coordinateRegister [])
        input.p input.source input.w.indexBits input.w.strideBits Lc)
      (reservoirClassLocalBank n H hfit w hw k (input.w.indexBits + input.w.strideBits) mate))
    (hleft : ∀ j, S.L (originalMatchingRepairEmbed TP₀ (matchingCoreEmbed TP₀ j)) = []) :
    ∃ (v' : HS (N₀ + 57) Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (reservoirClassLocalTableCost n w (input.w.indexBits + input.w.strideBits) : ℕ) +
        matchingPlacedRepairPrice input Lc + (2 * ((n - 3 * w) * (2 * (input.w.indexBits + input.w.strideBits) + 2)) + 2 : ℕ) ∧
      Exec body (originalMatchingPlacedProgram input (originalMatchingProducerEmbed TP₀)
        (originalMatchingRepairEmbed TP₀) ι₀ ι k reverse) (mk v S) steps
        (mk v' { S with R := Function.update S.R (originalMatchingRepairEmbed TP₀ (matchingCoreEmbed TP₀ str₀)) (moveRecs input.perm input.l).flatten }) := by
  apply originalMatchingPlacedRepair_exec input (originalMatchingProducerEmbed TP₀)
    (originalMatchingProducerEmbed_injective TP₀) (originalMatchingRepairEmbed TP₀)
    (originalMatchingRepairEmbed_injective TP₀) rfl ι₀ coreBody hcore ι body hbody
    n H hfit w hw k mate hinv hn hsize hsource hρ reverse htargets Lc hcountFit v S ?_ ?_ hleft
  · funext j
    change S.R (originalMatchingProducerEmbed TP₀ j) = _
    rw [hbank]
    apply originalMatchingInputBank_producer
    simp [reservoirClassLocalBank, reservoirMiddleProductionBank]
  · funext j
    change S.R (originalMatchingRepairEmbed TP₀ j) = _
    rw [hbank]
    exact originalMatchingInputBank_repair _ _ _ j

end
end IntegerMultBounds.MathlibTM2.Routing
