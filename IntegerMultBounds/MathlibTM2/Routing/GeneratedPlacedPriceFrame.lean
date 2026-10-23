module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedRepairPriceFrame
public import IntegerMultBounds.MathlibTM2.Routing.BinaryExchangeChain

/-! The complete generated/placed call budget is fixed by its metadata. Forward
and inverse placement prices and the generated core price ignore stream updates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {K : ℕ} {J : Type*} {t₀ T Q n : ℕ} {str tmp : Fin T}
variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def allSourcePlacedRepairPrice (scale wb wm wp wk R B Lrow Lwidth Lr Lm LK Ln Lo Lt : ℕ)
    (w : LiveDescriptorWidths) (calls : J → BinaryExchangeCall t₀ T Q n R B str tmp)
    (forward backward : List J) (M : Stacks T (prime + K))
    (E : Stacks inactiveProfileConfigurationT (prime + K)) : ℝ :=
  binaryExchangeChainCost calls M forward +
    allSourceGeneratedRepairPrice p X rb hG hK active s scale wb wm wp wk R B Lrow Lwidth Lr Lm LK Ln Lo Lt w E +
    binaryExchangeChainCost calls M backward

theorem allSourcePlacedRepairPrice_updateStream
    (scale wb wm wp wk R B Lrow Lwidth Lr Lm LK Ln Lo Lt : ℕ) (w : LiveDescriptorWidths)
    (calls : J → BinaryExchangeCall t₀ T Q n R B str tmp) (forward backward : List J)
    (M : Stacks T (prime + K)) (E : Stacks inactiveProfileConfigurationT (prime + K))
    (outerOut coreOut : List (Fin (prime + K + 4)))
    (hblank : ∀ j, RepairBlank j → E.R (inactiveConfigurationCore j) = []) :
    allSourcePlacedRepairPrice p X rb hG hK active s scale wb wm wp wk R B Lrow Lwidth Lr Lm LK Ln Lo Lt
        w calls forward backward { M with R := Function.update M.R str outerOut }
        { E with R := Function.update E.R (inactiveConfigurationCore repairHost.src) coreOut } =
      allSourcePlacedRepairPrice p X rb hG hK active s scale wb wm wp wk R B Lrow Lwidth Lr Lm LK Ln Lo Lt
        w calls forward backward M E := by
  unfold allSourcePlacedRepairPrice
  rw [binaryExchangeChainCost_updateStream,
    allSourceGeneratedRepairPrice_updateStream p X rb hG hK active s scale wb wm wp wk R B
      Lrow Lwidth Lr Lm LK Ln Lo Lt w E coreOut hblank,
    binaryExchangeChainCost_updateStream]

end
end IntegerMultBounds.MathlibTM2.Routing
