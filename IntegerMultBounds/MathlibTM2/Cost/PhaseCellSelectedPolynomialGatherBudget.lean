module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreGroupGatherBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreWidthCharge

/-! The complete actual gather bound needs only polynomial core width and
replica count below tensor volume, rather than quotient/exponent side gates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ}

theorem selectedPolynomialCoreGroupGatherCosts_le (hstates : FixedStreamedBank.stateCount ≤ Q) (cV cD cW C e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (V D a width radius L w : ℕ)
    (Fs : List (ZMod (Sizes.s n i) → GaussianInt)) (borrowed : List (Fin (prime+K+4)))
    (S : Stacks T (prime+K)) (g : GeometryRealGatherData (Q := Q) V (Sizes.s n i) width radius L w a D Fs borrowed S),
    width ≤ Sizes.s n i → radius ≤ width → (Sizes.p n)^2 ≤ width → L ≤ Sizes.s n i →
    V ≤ cV*Sizes.p n → D ≤ cD*Sizes.p n → w ≤ cW*Sizes.p n →
    D ≤ 2^a*2^Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius L).length*(L*w) →
    Fs.length ≤ Sizes.T n → width ≤ C*(Sizes.p n)^e →
    L ∈ coreGatherLengths (Sizes.s n i) width radius →
    (g.timeCost : ℝ) ≤ Sizes.T n+(coreExposureTrafficFactor cV cW+6013 : ℕ)*(Fs.length*Sizes.s n i*w : ℕ)+
      432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
        (Fs.length*Sizes.s n i*w : ℕ)*Sizes.d n*((Sizes.ℓ n : ℝ)^Parameters.tau+1) ∧
    g.stockAllowance ≤ Sizes.T n+
      (3*coreExposureTrafficFactor cV cW+12+12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*
        (Fs.length*Sizes.s n i*w) := by
  filter_upwards [selectedCoreGroupRealGatherCosts_le (T := T) (K := K) hstates cV cD cW,
    selectedPolynomialCoreWidth_quotient C e] with n hbill hquot
  intro h i V D a width radius L w Fs borrowed S g hwidth hradius hprepare hL hV hD hW hfit hvolume hpoly hgroup
  have ha := selectedReplicaExponent_le h a (by rw [←g.hreplicaPower]; exact hvolume)
  exact hbill h i V D a width radius L w Fs borrowed S g hwidth hradius hprepare hL hV hD hW hfit
    ha (hquot h i width g.hwidth hpoly) hgroup

end IntegerMultBounds.MathlibTM2.Cost
