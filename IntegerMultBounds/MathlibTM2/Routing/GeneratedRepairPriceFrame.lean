module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedRepairBankFrame
public import IntegerMultBounds.MathlibTM2.Routing.LiveCoordinateProfiles

/-! A named, stream-independent price for the full generated all-source repair
core: classifiers, widths, headers, source profiles, exact repair and cleanup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {K : ℕ}
variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def allSourceGeneratedRepairPrice (scale wb wm wp wk R B Lrow Lwidth Lr Lm LK Ln Lo Lt : ℕ)
    (w : LiveDescriptorWidths) (E : Stacks inactiveProfileConfigurationT (prime + K)) : ℝ :=
  (binaryTemporaryMaskCost p LK Ln Lo Lt + binaryPhaseMaskCost p LK Ln Lo Lt : ℕ) +
    ((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * p.wy + 11) + 2 * p.wy + 6) + 1 : ℕ) +
    (2 * (14 * (p.wc + p.wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) : ℕ) +
    (liveCoordinateProfilesCost p w : ℕ) +
    liveRepairPrice p X rb hG hK active s scale wb wm wp wk R B w
      (allSourceRepairPrepared p X rb R B hG hK active s w E) +
    (9 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 2 * (2 * (p.wc * (w.selectorBits + 3)) + 2) + 1 : ℕ) +
    (repairHeaderErasePrice p X rb R B : ℕ) + (2 * rb + 2 * p.wy + 5 : ℕ) + (4 * (p.wy + 1) + 5 : ℕ)

theorem allSourceGeneratedRepairPrice_updateStream
    (scale wb wm wp wk R B Lrow Lwidth Lr Lm LK Ln Lo Lt : ℕ) (w : LiveDescriptorWidths)
    (E : Stacks inactiveProfileConfigurationT (prime + K)) (out : List (Fin (prime + K + 4)))
    (hblank : ∀ j, RepairBlank j → E.R (inactiveConfigurationCore j) = []) :
    allSourceGeneratedRepairPrice p X rb hG hK active s scale wb wm wp wk R B Lrow Lwidth Lr Lm LK Ln Lo Lt w
        { E with R := Function.update E.R (inactiveConfigurationCore repairHost.src) out } =
      allSourceGeneratedRepairPrice p X rb hG hK active s scale wb wm wp wk R B Lrow Lwidth Lr Lm LK Ln Lo Lt w E := by
  unfold allSourceGeneratedRepairPrice
  rw [allSourceRepairPrepared_updateStream,
    liveRepairPrice_updateStream p X rb hG hK active s scale wb wm wp wk R B w _ out
      (allSourceRepairPrepared_blank p X rb R B hG hK active s w E hblank)]

end
end IntegerMultBounds.MathlibTM2.Routing
