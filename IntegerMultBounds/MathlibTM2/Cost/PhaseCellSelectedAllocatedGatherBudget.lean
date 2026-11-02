module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedGatherMetadataCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreExposureTraffic
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeometryGatherBudget

/-! The actual fresh-bank gather includes metadata loading and retirement.
Their cost is source-linear and adds no dyadic routing factor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose ScalarPlacement.ComputedClassBanks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ}

theorem selectedAllocatedRealGatherCosts_le (hstates : FixedStreamedBank.stateCount ≤ Q) (cV cD cW : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (V D a width radius L w : ℕ)
    (bank : ScalarPlacement.ComputedClassBank → Fin T)
    (Fs : List (ZMod (Sizes.s n i) → GaussianInt)) (borrowed : List (Fin (prime+K+4)))
    (S : Stacks (T+PackedTranspose.tapeCount) (prime+K))
    (g : AllocatedRealGatherData (Q := Q) bank V (Sizes.s n i) width radius L w a D Fs borrowed S),
    width ≤ Sizes.s n i → radius ≤ width → (Sizes.p n)^2 ≤ width → L ≤ Sizes.s n i →
    V ≤ cV*Sizes.p n → D ≤ cD*Sizes.p n → w ≤ cW*Sizes.p n →
    D ≤ 2^a*2^Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius L).length*(L*w) →
    let b := Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius L).length
    (g.timeCost : ℝ) ≤ Sizes.T n+(coreExposureTrafficFactor cV cW+48*cD+6095 : ℕ)*(Fs.length*Sizes.s n i*w : ℕ)+
      24*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
        (Fs.length*Sizes.s n i*w : ℕ)*dyadicRouteCharge a b ∧
    g.stockAllowance ≤ Sizes.T n+
      (3*coreExposureTrafficFactor cV cW+72*cD+134+
        12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*Sizes.s n i*w) := by
  filter_upwards [selectedGeometryGatherCosts_le hstates cD] with n hgeometry
  intro h i V D a width radius L w bank Fs borrowed S g hwidth hradius hprepare hL hV hD hW hfit
  dsimp only
  have hs : 1 ≤ Sizes.s n i := g.hwidth.trans_le hwidth
  have hw : 1 ≤ w := by
    by_contra hn
    have hz : w = 0 := by omega
    have hp := g.hpacket
    simp [hz] at hp
  have hB : 0 < Fs.length := by rw [g.hreplicaPower]; exact Nat.two_pow_pos _
  let source := Fs.length*Sizes.s n i*w
  have hsource : 1 ≤ source := Nat.mul_le_mul (Nat.mul_pos hB hs) hw
  have hsSource : Sizes.s n i ≤ source := by
    have hh := Nat.mul_le_mul (Nat.le_mul_of_pos_left (Sizes.s n i) hB) hw
    simpa only [Nat.mul_one] using hh
  have hwSource : w ≤ source := Nat.le_mul_of_pos_left _ (Nat.mul_pos hB hs)
  have hBSource : Fs.length ≤ source := by
    have hh := Nat.mul_le_mul (Nat.le_mul_of_pos_right Fs.length hs) hw
    simpa only [Nat.mul_one] using hh
  have hp : Sizes.p n ≤ source :=
    ((Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) _).trans hprepare).trans (hwidth.trans hsSource)
  have hDSource := hD.trans (Nat.mul_le_mul_left cD hp)
  have htMeta : 8*gatherMetadataVolume g.src S+66 ≤ (48*cD+82)*source := by
    rw [g.metadataVolume_eq]
    nlinarith only [hDSource,hwSource,hBSource,hsource]
  have hsMeta : 12*gatherMetadataVolume g.src S+98 ≤ (72*cD+122)*source := by
    rw [g.metadataVolume_eq]
    nlinarith only [hDSource,hwSource,hBSource,hsource]
  obtain ⟨htExposure,hsExposure⟩ := replicaCoreExposureCosts_le_source cV cW (Sizes.p n) V (Sizes.s n i)
    width radius L w Fs.length g.hVpos hs hw g.hwidth hwidth hradius hprepare hL hV hW hB g.hgroup
  obtain ⟨htRoute,hsRoute⟩ := hgeometry h i D a width radius L w g.hwidth hwidth hradius hD g.hgroup g.hpacket hfit
  rw [←g.hreplicaPower] at htRoute hsRoute
  constructor
  · have htExposureR := (Nat.cast_le (α := ℝ)).mpr htExposure
    have htMetaR := (Nat.cast_le (α := ℝ)).mpr htMeta
    have hsourceR := (Nat.cast_le (α := ℝ)).mpr hsource
    unfold AllocatedRealGatherData.timeCost RealGatherExposureData.timeCost
    dsimp only [source] at htMetaR hsourceR
    push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] at htExposureR htMetaR hsourceR htRoute ⊢
    nlinarith only [htExposureR,htMetaR,htRoute,hsourceR]
  · unfold AllocatedRealGatherData.stockAllowance RealGatherExposureData.stockAllowance
    dsimp only [source] at hsMeta hsource
    nlinarith only [hsExposure,hsMeta,hsRoute,hsource]

end IntegerMultBounds.MathlibTM2.Cost
