module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCoreOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationGeometryControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationDimensions
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPublicationMetadataCost

/-! Shared publication controls are scalar work, generated once per class.
Their polynomial bounds are independent of replica count and coefficient data. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellMatrix

private theorem preparedOriginsCost_le {V s width radius L t cV : ℕ}
    (ht : 1 ≤ t) (hs : s ≤ t) (hwidth : 0 < width) (hV : V ≤ cV*t) :
    preparedCoreOriginsCost V s width radius L ≤
      (27*(32*(cV+4)^2+8*cV)+182*cV+212)*t^3 := by
  have hcount : (s+width-1)/width ≤ s := by
    simpa only [coreIndices,List.length_range] using coreIndices_length_le s width hwidth
  have hkeys := coreGatherIndices_length_le s width radius L hwidth
  have hwidthV : V+4 ≤ (cV+4)*t := by nlinarith only [hV,ht]
  have hpow := Nat.pow_le_pow_left hwidthV 2
  have htSq : t ≤ t^2 := Nat.le_self_pow (by decide) t
  have htable : tblC V V ≤ (32*(cV+4)^2+8*cV)*t^2 := by
    have hVsq := hV.trans (Nat.mul_le_mul_left cV htSq)
    unfold tblC
    nlinarith only [hpow,hVsq]
  have hloop : 18*((s+width-1)/width)+9 ≤ 27*t := by omega
  have hloopCost := Nat.mul_le_mul hloop htable
  have hkeyCost := Nat.mul_le_mul (hkeys.trans hs)
    (show 8*V+6 ≤ (8*cV+6)*t by nlinarith only [hV,ht])
  have htCube : t^2 ≤ t^3 := Nat.pow_le_pow_right ht (by decide)
  have htToCube := htSq.trans htCube
  have hVCube := hV.trans (Nat.mul_le_mul_left cV htToCube)
  have hone : 1 ≤ t^3 := ht.trans htToCube
  have hkeyCube := (Nat.mul_le_mul_left (8*cV+6) htCube)
  unfold preparedCoreOriginsCost
  nlinarith only [hloopCost,hkeyCost,hVCube,hone,hkeyCube]

theorem selectedPreparedCoreOriginsCost_le (cV : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ V width radius L : ℕ, 0 < width → V ≤ cV*Sizes.p n →
      preparedCoreOriginsCost V (Sizes.s n i) width radius L ≤ Sizes.T n := by
  let C := 27*(32*(cV+4)^2+8*cV)+182*cV+212
  filter_upwards [selectedAxisPolynomial_le_volume C 0 3] with n hn
  intro h i V width radius L hwidth hV
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hpt := selectedPrecision_le_axis h i
  have hc := preparedOriginsCost_le (hp.trans hpt) (h.good.lt i).le hwidth
    (hV.trans (Nat.mul_le_mul_left cV hpt)) (radius := radius) (L := L)
  exact hc.trans (by simpa only [pow_zero,mul_one] using hn i)

theorem selectedPublicationControlCosts_le (cV : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ V k b N L radius : ℕ, k ≤ Sizes.s n i → 2^b = N →
      L ≤ 3*Sizes.s n i → radius ≤ Sizes.s n i → V ≤ cV*Sizes.p n →
      PublicationGeometryControls.timeCost V (Sizes.s n i) L radius ≤ Sizes.T n ∧
      2*((L-2*radius)+Sizes.s n i)+5 ≤ Sizes.T n ∧
      PackedTranspose.publicationDimensionsTimeCost b k ≤ Sizes.T n+19*N ∧
      2*(b+Nat.clog 2 k+2^Nat.clog 2 k)+7 ≤ Sizes.T n+2*N ∧
      2*(k*V+k)+5 ≤ Sizes.T n := by
  filter_upwards [selectedAxisPolynomial_le_volume (76+33*cV) 0 1,
    selectedAxisPolynomial_le_volume 13 0 1,
    selectedAxisPolynomial_le_volume 82 0 1,
    selectedAxisPolynomial_le_volume 19 0 1,
    selectedAxisPolynomial_le_volume (2*cV+7) 0 2] with n hg hr hd hrd ho
  intro h i V k b N L radius hk hb hL hradius hV
  let t := Sizes.t n i
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hpt := selectedPrecision_le_axis h i
  have ht : 1 ≤ t := hp.trans hpt
  have hs : Sizes.s n i ≤ t := (h.good.lt i).le
  have hkT := hk.trans hs
  have hLT := hL.trans (Nat.mul_le_mul_left 3 hs)
  have hrT := hradius.trans hs
  have hVT := hV.trans (Nat.mul_le_mul_left cV hpt)
  have hgeom : PublicationGeometryControls.timeCost V (Sizes.s n i) L radius ≤ (76+33*cV)*t := by
    unfold PublicationGeometryControls.timeCost prepareCoreDimensionsCost
    nlinarith only [hLT,hrT,hs,hVT,ht]
  have hretire : 2*((L-2*radius)+Sizes.s n i)+5 ≤ 13*t := by
    have hcore := (Nat.sub_le L (2*radius)).trans hLT
    omega
  have hpad := pow_clog_two_le k
  have ha : Nat.clog 2 k ≤ 2^Nat.clog 2 k := Nat.lt_two_pow_self.le
  have hbSmall : b ≤ N := Nat.lt_two_pow_self.le.trans_eq hb
  have hdim : PackedTranspose.publicationDimensionsTimeCost b k ≤ 82*t+19*N := by
    unfold PackedTranspose.publicationDimensionsTimeCost
    rw [hb]
    omega
  have hdimRetire : 2*(b+Nat.clog 2 k+2^Nat.clog 2 k)+7 ≤ 19*t+2*N := by omega
  have hprod := Nat.mul_le_mul hkT hVT
  have htSq : t ≤ t^2 := Nat.le_self_pow (by decide) t
  have hone : 1 ≤ t^2 := ht.trans htSq
  have horigin : 2*(k*V+k)+5 ≤ (2*cV+7)*t^2 := by
    nlinarith only [hprod,hkT,htSq,hone]
  have hgV : (76+33*cV)*t ≤ Sizes.T n := by simpa only [pow_zero,pow_one,mul_one] using hg i
  have hrV : 13*t ≤ Sizes.T n := by simpa only [pow_zero,pow_one,mul_one] using hr i
  have hdV : 82*t ≤ Sizes.T n := by simpa only [pow_zero,pow_one,mul_one] using hd i
  have hrdV : 19*t ≤ Sizes.T n := by simpa only [pow_zero,pow_one,mul_one] using hrd i
  have hoV : (2*cV+7)*t^2 ≤ Sizes.T n := by simpa only [pow_zero,mul_one] using ho i
  exact ⟨hgeom.trans hgV,hretire.trans hrV,hdim.trans (Nat.add_le_add_right hdV _),
    hdimRetire.trans (Nat.add_le_add_right hrdV _),horigin.trans hoV⟩

end IntegerMultBounds.MathlibTM2.Cost
