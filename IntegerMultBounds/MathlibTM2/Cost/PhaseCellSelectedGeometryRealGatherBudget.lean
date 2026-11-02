module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreExposureTraffic
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

theorem selectedGeometryRealGatherCosts_le (hstates : FixedStreamedBank.stateCount ≤ Q) (cV cD cW : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (V D a width radius L w : ℕ)
    (Fs : List (ZMod (Sizes.s n i) → GaussianInt)) (borrowed : List (Fin (prime+K+4)))
    (S : Stacks T (prime+K)) (g : GeometryRealGatherData (Q := Q) V (Sizes.s n i) width radius L w a D Fs borrowed S),
    width ≤ Sizes.s n i → radius ≤ width → (Sizes.p n)^2 ≤ width → L ≤ Sizes.s n i →
    V ≤ cV*Sizes.p n → D ≤ cD*Sizes.p n → w ≤ cW*Sizes.p n →
    D ≤ 2^a*2^Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius L).length*(L*w) →
    let b := Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius L).length
    (g.timeCost : ℝ) ≤ Sizes.T n+(coreExposureTrafficFactor cV cW+6013 : ℕ)*(Fs.length*Sizes.s n i*w : ℕ)+
      24*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
        (Fs.length*Sizes.s n i*w : ℕ)*dyadicRouteCharge a b ∧
    g.stockAllowance ≤ Sizes.T n+
      (3*coreExposureTrafficFactor cV cW+12+12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*
        (Fs.length*Sizes.s n i*w) := by
  filter_upwards [selectedGeometryGatherCosts_le hstates cD] with n hgeometry
  intro h i V D a width radius L w Fs borrowed S g hwidth hradius hprepare hL hV hD hW hfit
  dsimp only
  have hs : 1 ≤ Sizes.s n i := g.hwidth.trans_le hwidth
  have hw : 1 ≤ w := by
    by_contra hn
    have hz : w = 0 := by omega
    have hp := g.hpacket
    simp [hz] at hp
  have hB : 0 < Fs.length := by rw [g.hreplicaPower]; exact Nat.two_pow_pos _
  have hsource : 1 ≤ Fs.length*Sizes.s n i*w := Nat.mul_le_mul (Nat.mul_pos hB hs) hw
  obtain ⟨htExposure,hsExposure⟩ := replicaCoreExposureCosts_le_source cV cW (Sizes.p n) V (Sizes.s n i)
    width radius L w Fs.length g.hVpos hs hw g.hwidth hwidth hradius hprepare hL hV hW hB g.hgroup
  obtain ⟨htRoute,hsRoute⟩ := hgeometry h i D a width radius L w g.hwidth hwidth hradius hD g.hgroup g.hpacket hfit
  rw [←g.hreplicaPower] at htRoute hsRoute
  constructor
  · have htExposureR := (Nat.cast_le (α := ℝ)).mpr htExposure
    have hsourceR := (Nat.cast_le (α := ℝ)).mpr hsource
    unfold GeometryRealGatherData.timeCost
    push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] at htExposureR hsourceR htRoute ⊢
    nlinarith only [htExposureR,htRoute,hsourceR]
  · unfold GeometryRealGatherData.stockAllowance
    nlinarith only [hsExposure,hsRoute,hsource]

end IntegerMultBounds.MathlibTM2.Cost
