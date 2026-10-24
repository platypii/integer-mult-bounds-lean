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

def allSourceGeneratedUniformOverhead (n wb wm wp wk R B width Lrow Lwidth Lr Lm LK Ln Lo Lt : ℕ)
    (w : LiveDescriptorWidths) : ℕ :=
  binaryTemporaryMaskCost p LK Ln Lo Lt + binaryPhaseMaskCost p LK Ln Lo Lt +
    ((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * p.wy + 11) + 2 * p.wy + 6) + 1) +
    2 * (14 * (p.wc + p.wy + X) + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) +
    liveCoordinateProfilesCost p w + liveRepairUniformOverhead n rb R B width wb wm wp wk w +
    (9 * (2 * (p.n * (w.selectorBits + 3)) + 2) + 2 * (2 * (p.wc * (w.selectorBits + 3)) + 2) + 1) +
    (10 * (2 * width + 2) + 1) + (2 * rb + 2 * p.wy + 5) + (4 * (p.wy + 1) + 5)

theorem allSourceGeneratedUniformOverhead_le
    (n wb wm wp wk R B width Lrow Lwidth Lr Lm LK Ln Lo Lt classifierBound profileBound Ls : ℕ)
    (w : LiveDescriptorWidths) (hsize : p.wc + p.wy + X ≤ n)
    (hslots : p.n ≤ n) (hselector : w.selectorBits ≤ Ls)
    (hclassifier : binaryTemporaryMaskCost p LK Ln Lo Lt + binaryPhaseMaskCost p LK Ln Lo Lt ≤ classifierBound)
    (hprofile : liveCoordinateProfilesCost p w ≤ profileBound) :
    allSourceGeneratedUniformOverhead p X rb n wb wm wp wk R B width
      Lrow Lwidth Lr Lm LK Ln Lo Lt w ≤
      classifierBound +
      ((Lr * (4 * rb + 11) + 8 * rb + 12) + (Lm * (4 * n + 11) + 2 * n + 6) + 1) +
      2 * (14 * n + 18 * Lrow + 24 * Lwidth + 52 * wb + 280) +
      profileBound + liveRepairUniformOverhead n rb R B width wb wm wp wk w +
      (11 * (2 * (n * (Ls + 3)) + 2) + 1) +
      (10 * (2 * width + 2) + 1) + (2 * rb + 2 * n + 5) + (4 * (n + 1) + 5) := by
  have hwy : p.wy ≤ n := by omega
  have hwc : p.wc ≤ n := by omega
  have hwidth : Lm * (4 * p.wy + 11) ≤ Lm * (4 * n + 11) :=
    Nat.mul_le_mul_left Lm (by omega)
  have hs : w.selectorBits + 3 ≤ Ls + 3 := by omega
  have hn := Nat.mul_le_mul hslots hs
  have hc := Nat.mul_le_mul hwc hs
  unfold allSourceGeneratedUniformOverhead
  omega

theorem allSourceGeneratedRepairPrice_le
    (scale wb wm wp wk R B width Lrow Lwidth Lr Lm LK Ln Lo Lt n : ℕ)
    (w : LiveDescriptorWidths) (E : Stacks inactiveProfileConfigurationT (prime + K))
    (hGK : p.G < p.K)
    (hfields : IntegerMultBounds.MathlibTM2.Layer.CompactDigits.fieldsLen (selectiveLen p X) = n)
    (hn : p.n ≤ n) (hgroup : p.n * p.G ≤ n)
    (hfit : ∀ j, LiveDescriptorBounds p X w (repairLiveMode j))
    (headers : Fin 2 → Fin 5 → List Bool)
    (data : RepairPendingMaskData p X rb wb wm wp wk R B headers
      (fun j => E.R (inactiveConfigurationCore j)))
    (hdesc : ∀ d, E.R (inactiveConfigurationCore (repairDescriptorSource d)) = [])
    (hleft : ∀ j, E.L (inactiveConfigurationCore j) = [])
    (hblank : ∀ j, RepairBlank j → E.R (inactiveConfigurationCore j) = [])
    (hheaders : ∀ c k, (repairCanonicalHeaders p X rb R B c k).length ≤ width) :
    allSourceGeneratedRepairPrice p X rb hG hK active s scale wb wm wp wk R B
      Lrow Lwidth Lr Lm LK Ln Lo Lt w E ≤
      (allSourceGeneratedUniformOverhead p X rb n wb wm wp wk R B width
        Lrow Lwidth Lr Lm LK Ln Lo Lt w : ℕ) +
      (selectiveUniformKeyPassCost n rb (R * 2 ^ n) B : ℕ) +
      (12 * (selectiveUniformRotationCost n (R * 2 ^ n) (n + rb + B) : ℕ) +
        12 * selectiveUniformSwapCost repairT (R * 2 ^ n) (n + rb + B) p.wc
          (swapT 6 * (width + 1)) + 1) +
      repairUniformDensityScanCost n rb R B scale := by
  have hr := allSourceRepairPrepared_price_le p X rb R B hG hK active s w E
    scale wb wm wp wk n width hGK hfields hn hgroup hfit headers data hdesc hleft hblank hheaders
  have hh : (repairHeaderErasePrice p X rb R B : ℝ) ≤ (10 * (2 * width + 2) + 1 : ℕ) :=
    Nat.cast_le.mpr (repairHeaderErasePrice_le p X rb R B width hheaders)
  dsimp only [allSourceGeneratedRepairPrice, allSourceGeneratedUniformOverhead]
  simp only [Nat.cast_add] at hr hh ⊢
  linarith only [hr, hh]

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
