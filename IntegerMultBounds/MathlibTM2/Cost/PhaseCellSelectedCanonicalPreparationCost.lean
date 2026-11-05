module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCanonicalInputPreparationCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawHeaderVolume
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreHeaderWidth

/-! Shared canonical setup is absorbed once in box volume; copying remains
linear in the number of input cells at the selected precision. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedCanonicalInputPreparationTime_le (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target N : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      canonicalInputPreparationTime (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        target (Sizes.s n i) (Sizes.t n i) N ≤
        Sizes.T n+(60*(1032+8*ct))*(N*Sizes.s n i*Sizes.p n) := by
  let cB := 2*(ct+21)+22
  let cW := 1032+8*ct
  let c := (ct+25)*(4*cB+10)+284*cB+12*cW+366
  filter_upwards [selectedRawHeaderCost_scaled_volume_le ct 2,
    selectedAxisPolynomial_le_volume (2*c) 1 1] with n hnHeader hnScalar
  intro h i _ u target N hu htarget hband
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let B := inverseCallerWordWidth p u l target s t
  let W := packedHaloCommonWidth p l s u (target+1) 2
  let H := inverseScalarAtoms p s t u 0 s*tblC B 0+
    inverseMasterCopyCost B (inverseMasterValues p u l target s t 0 s)+
    inverseReleaseCost B (inverseMasterValues p u l target s t 0 s)
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hpt : p ≤ t := selectedPrecision_le_axis h i
  have ht : 1 ≤ t := hp.trans hpt
  have hst : s ≤ t := (h.good.lt i).le
  have hB : B ≤ cB*p := selectedInverseCallerWordWidth_le ct h i hu htarget hband
  have hW : W ≤ cW*p := selectedPackedHaloCommonWidth_le ct h i u target htarget hband
  have hl := (haloInverseRingLog_bounds hp (h.good.lt i) (h.quarter_p_le_theta i)).1
  have hscan : p+u+l+target+s+t+0+s ≤ (ct+25)*t := by
    have huT := hu.trans hpt
    have htargetT := htarget.trans (Nat.mul_le_mul_left ct hpt)
    have hlT := hl.trans (Nat.mul_le_mul_left 20 hpt)
    nlinarith only [hpt,huT,htargetT,hlT,hst]
  have hword : 4*B+10 ≤ (4*cB+10)*p := by nlinarith only [hB,hp]
  have hprod := Nat.mul_le_mul hscan hword
  have hptMul : p ≤ t*p := Nat.le_mul_of_pos_left p ht
  have hone : 1 ≤ t*p := hp.trans hptMul
  have hlinear : 284*B+12*W+366 ≤ (284*cB+12*cW+366)*(t*p) := by
    have hBT := hB.trans (Nat.mul_le_mul_left cB hptMul)
    have hWT := hW.trans (Nat.mul_le_mul_left cW hptMul)
    nlinarith only [hBT,hWT,hone]
  have hscalar : (p+u+l+target+s+t+0+s)*(4*B+10)+284*B+12*W+366 ≤ c*t*p := by
    dsimp only [c]
    nlinarith only [hprod,hlinear]
  have hretire : callerInputMasterRetireCost p u l target s t ≤
      inverseReleaseCost B (inverseMasterValues p u l target s t 0 s) := by
    unfold callerInputMasterRetireCost inverseReleaseCost
    rw [List.ofFn_eq_map]
    omega
  have hc := canonicalInputPreparationTime_le (s := s) p u l target t N
  have htraffic := Nat.mul_le_mul_left (60*N*s) hW
  have hh : 2*H ≤ Sizes.T n := hnHeader h i u target hu htarget hband
  have hs : 2*c*t*p ≤ Sizes.T n := by
    simpa only [pow_one] using hnScalar i
  dsimp only at hc
  unfold generateInverseMastersCost at hc
  dsimp only [H] at hh
  dsimp only [B,W,cW,p,s,t,l] at hc hretire hscalar htraffic hh hs ⊢
  nlinarith only [hc,hretire,hscalar,htraffic,hh,hs]

end IntegerMultBounds.MathlibTM2.Cost
