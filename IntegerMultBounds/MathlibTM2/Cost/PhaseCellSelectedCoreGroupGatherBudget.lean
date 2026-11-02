module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreRouteCharge
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeometryRealGatherBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeometryGatherBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryRealGatherData

/-! Complete actual ambient gather: selected setup is paid globally, restoring
exposure is source-linear and routing retains only its sharp dyadic charge. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ}

theorem selectedCoreGroupRealGatherCosts_le (hstates : FixedStreamedBank.stateCount ≤ Q) (cV cD cW : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (V D a width radius L w : ℕ)
    (Fs : List (ZMod (Sizes.s n i) → GaussianInt)) (borrowed : List (Fin (prime+K+4)))
    (S : Stacks T (prime+K)) (g : GeometryRealGatherData (Q := Q) V (Sizes.s n i) width radius L w a D Fs borrowed S),
    width ≤ Sizes.s n i → radius ≤ width → (Sizes.p n)^2 ≤ width → L ≤ Sizes.s n i →
    V ≤ cV*Sizes.p n → D ≤ cD*Sizes.p n → w ≤ cW*Sizes.p n →
    D ≤ 2^a*2^Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius L).length*(L*w) →
    a ≤ Sizes.d n*Sizes.ℓ n →
    2^((Sizes.ℓ n+1)/2)+2 ≤ Sizes.s n i/width →
    L ∈ coreGatherLengths (Sizes.s n i) width radius →
    (g.timeCost : ℝ) ≤ Sizes.T n+(coreExposureTrafficFactor cV cW+6013 : ℕ)*(Fs.length*Sizes.s n i*w : ℕ)+
      432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
        (Fs.length*Sizes.s n i*w : ℕ)*Sizes.d n*((Sizes.ℓ n : ℝ)^Parameters.tau+1) ∧
    g.stockAllowance ≤ Sizes.T n+
      (3*coreExposureTrafficFactor cV cW+12+12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*
        (Fs.length*Sizes.s n i*w) := by
  filter_upwards [selectedGeometryRealGatherCosts_le (T := T) (K := K) hstates cV cD cW] with n hbill
  intro h i V D a width radius L w Fs borrowed S g hwidth hradius hprepare hL hV hD hW hfit ha hquot hgroup
  obtain ⟨ht,hs⟩ := hbill h i V D a width radius L w Fs borrowed S g hwidth hradius hprepare hL hV hD hW hfit
  have hcharge := selectedCoreGroupRouteCharge_le h i a width radius L ha g.hwidth hradius hquot hgroup
  have hc : 0 ≤ 24*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
      (Fs.length*Sizes.s n i*w : ℕ) := by
    have := IntegerMultBounds.MathlibTM2.Node.swapConst_pos
    unfold generatedDyadicStageCoeff
    positivity
  have hm := mul_le_mul_of_nonneg_left hcharge hc
  exact ⟨by nlinarith only [ht,hm],hs⟩

end IntegerMultBounds.MathlibTM2.Cost
