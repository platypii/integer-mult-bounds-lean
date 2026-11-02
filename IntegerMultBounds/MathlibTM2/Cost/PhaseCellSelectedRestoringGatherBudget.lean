module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringGatherMetadataCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreExposureTraffic
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeometryGatherBudget

/-! The complete restoring preparation pays both exposure and routing metadata
lifecycles. These costs add source-linear traffic without a new routing factor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix
open PackedTranspose ScalarPlacement.ComputedClassBanks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ}

theorem selectedRestoringGatherCosts_le (hstates : FixedStreamedBank.stateCount ≤ Q) (cV cD cW : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) (V width radius L w : ℕ)
    (bank : ScalarPlacement.ComputedClassBank → Fin T)
    (Fs : List (ZMod (Sizes.s n i) → GaussianInt)) (borrowed : List (Fin (prime+K+4)))
    (S : Stacks ((T+175)+PackedTranspose.tapeCount) (prime+K))
    (g : RestoringGatherData (Q := Q) bank V (Sizes.s n i) width radius L w Fs borrowed S),
    width ≤ Sizes.s n i → radius ≤ width → (Sizes.p n)^2 ≤ width → L ≤ Sizes.s n i →
    V ≤ cV*Sizes.p n → g.D ≤ cD*Sizes.p n → w ≤ cW*Sizes.p n →
    g.D ≤ 2^g.a*2^Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius L).length*(L*w) →
    let b := Nat.clog 2 (coreGatherIndices (Sizes.s n i) width radius L).length
    (g.timeCost : ℝ) ≤ Sizes.T n+(coreExposureTrafficFactor cV cW+40*cV+48*cD+6185 : ℕ)*(Fs.length*Sizes.s n i*w : ℕ)+
      24*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
        (Fs.length*Sizes.s n i*w : ℕ)*dyadicRouteCharge g.a b ∧
    g.stockAllowance ≤ Sizes.T n+
      (3*coreExposureTrafficFactor cV cW+60*cV+72*cD+268+
        12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*Sizes.s n i*w) := by
  filter_upwards [selectedGeometryGatherCosts_le hstates cD] with n hgeometry
  intro h i V width radius L w bank Fs borrowed S g hwidth hradius hprepare hL hV hD hW hfit
  dsimp only
  have hs : 1 ≤ Sizes.s n i := g.hwidth.trans_le hwidth
  have hw : 1 ≤ w := by
    by_contra hn
    have hz : w = 0 := by omega
    have hp := g.hpacket
    simp [hz] at hp
  have hB : 0 < Fs.length := by rw [g.hpower]; exact Nat.two_pow_pos _
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
  have hVSource := hV.trans (Nat.mul_le_mul_left cV hp)
  have hlineSource : Sizes.s n i*w ≤ source := by
    simpa only [source,Nat.mul_assoc] using Nat.le_mul_of_pos_left (Sizes.s n i*w) hB
  have htMeta : (8*exposureMetadataVolume g.exposeSrc (embStk (exposureIntoRouting T) S)+66)+
      (8*gatherMetadataVolume (fun j => Fin.castAdd 175 (g.routeSrc j)) S+66) ≤
        (40*cV+48*cD+172)*source := by
    rw [g.exposureMetadataVolume_eq,g.routingMetadataVolume_eq]
    nlinarith only [hDSource,hVSource,hwSource,hBSource,hlineSource,hsource]
  have hsMeta : (12*exposureMetadataVolume g.exposeSrc (embStk (exposureIntoRouting T) S)+98)+
      (12*gatherMetadataVolume (fun j => Fin.castAdd 175 (g.routeSrc j)) S+98) ≤
        (60*cV+72*cD+256)*source := by
    rw [g.exposureMetadataVolume_eq,g.routingMetadataVolume_eq]
    nlinarith only [hDSource,hVSource,hwSource,hBSource,hlineSource,hsource]
  obtain ⟨htExposure,hsExposure⟩ := replicaCoreExposureCosts_le_source cV cW (Sizes.p n) V (Sizes.s n i)
    width radius L w Fs.length g.hVpos hs hw g.hwidth hwidth hradius hprepare hL hV hW hB g.hgroup
  obtain ⟨htRoute,hsRoute⟩ := hgeometry h i g.D g.a width radius L w g.hwidth hwidth hradius hD g.hgroup g.hpacket hfit
  rw [←g.hpower] at htRoute hsRoute
  constructor
  · have htExposureR := (Nat.cast_le (α := ℝ)).mpr htExposure
    have htMetaR := (Nat.cast_le (α := ℝ)).mpr htMeta
    have hsourceR := (Nat.cast_le (α := ℝ)).mpr hsource
    unfold RestoringGatherData.timeCost
    dsimp only [source] at htMetaR hsourceR
    push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] at htExposureR htMetaR hsourceR htRoute ⊢
    nlinarith only [htExposureR,htMetaR,htRoute,hsourceR]
  · unfold RestoringGatherData.stockAllowance
    dsimp only [source] at hsMeta hsource
    nlinarith only [hsExposure,hsMeta,hsRoute,hsource]

end IntegerMultBounds.MathlibTM2.Cost
