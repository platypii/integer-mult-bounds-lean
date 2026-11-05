module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBoundaryControlCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedHaloCommonWidth
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Shared boundary scalars fit in root volume. Replica traffic keeps its
linear charge; the format-width hypothesis is explicit for root instantiation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

private theorem boundaryScalarCosts_le {p s t D cD cW W : ℕ}
    (hp : 1 ≤ p) (hpt : p ≤ t) (hst : s ≤ t) (hD : D ≤ cD*t) (hW : W ≤ cW*p) :
    let Ktime := 1536*(cD+4)^2+384*cD+1463
    let Kstock := 4608*(cD+4)^2+962*cD+3917
    let KpubTime := 1536*(cD+4)^2+350*cD+1335*cW+104
    let KpubStock := 6656*(cD+4)^2+1426*cD+5597*cW+134
    boundaryControlTimeBound p D s ≤ Ktime*t^2 ∧
    boundaryControlStockBound p D s ≤ Kstock*t^2 ∧
    48*tblC D 0+350*D+1335*s*W+104 ≤ KpubTime*t^2 ∧
    208*tblC D 0+1426*D+5597*s*W+134 ≤ KpubStock*t^2 := by
  have ht : 1 ≤ t := hp.trans hpt
  have htSq : t ≤ t^2 := Nat.le_self_pow (by decide) t
  have hone : 1 ≤ t^2 := ht.trans htSq
  have hDsq := hD.trans (Nat.mul_le_mul_left cD htSq)
  have hwidth : D+4 ≤ (cD+4)*t := by nlinarith only [hD,ht]
  have hpow := Nat.pow_le_pow_left hwidth 2
  have htable : tblC D 0 ≤ 32*(cD+4)^2*t^2 := by
    unfold tblC
    nlinarith only [hpow]
  have hw : 2*p+13 ≤ 15*t := by omega
  have hsw := Nat.mul_le_mul hst hw
  have hfactor : 4*D+10 ≤ (4*cD+10)*t := by nlinarith only [hD,ht]
  have hprod := Nat.mul_le_mul hfactor hw
  have hsW := Nat.mul_le_mul hst (hW.trans (Nat.mul_le_mul_left cW hpt))
  dsimp only
  unfold boundaryControlTimeBound boundaryControlStockBound
  constructor
  · nlinarith only [htable,hDsq,hsw,hprod,hone]
  constructor
  · nlinarith only [htable,hDsq,hsw,hone]
  constructor <;> nlinarith only [htable,hDsq,hsW,hone]

/-- The same width fits the data format and every counter bounded by `x`. -/
theorem volumeCounterFormat_fits (B x : ℕ) :
    B ≤ max B (Nat.size x) ∧ ∀ v ≤ x, v < 2^(max B (Nat.size x)) := by
  refine ⟨le_max_left _ _,?_⟩
  intro v hv
  exact hv.trans_lt ((Nat.lt_size_self x).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_right B (Nat.size x))))

/-- A counter for data bounded by root volume fits within selected precision. -/
theorem selectedVolumeCounterWidth_le {n x : ℕ} (h : Sizes.Big n) (hx : x ≤ Sizes.T n) :
    Nat.size x ≤ Sizes.p n := by
  have hlog : Sizes.logT n < Sizes.p n := by
    have hb := h.logT_bounds.2
    unfold Sizes.p
    omega
  apply Nat.size_le.mpr
  exact hx.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hlog)

/-- Combine the data-format width and a generated volume counter. -/
theorem selectedDimensionWidth_le_precision (cFormat : ℕ) {n B x : ℕ} (h : Sizes.Big n)
    (hB : B ≤ cFormat*Sizes.p n) (hx : x ≤ Sizes.T n) :
    max B (Nat.size x) ≤ (cFormat+1)*Sizes.p n := by
  have hcounter := selectedVolumeCounterWidth_le h hx
  apply max_le
  · nlinarith only [hB]
  · nlinarith only [hcounter]

theorem selectedDimensionWidth_le_axis (cFormat : ℕ) {n B x : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) (hB : B ≤ cFormat*Sizes.p n) (hx : x ≤ Sizes.T n) :
    max B (Nat.size x) ≤ (cFormat+1)*Sizes.t n i :=
  (selectedDimensionWidth_le_precision cFormat h hB hx).trans
    (Nat.mul_le_mul_left _ (selectedPrecision_le_axis h i))

theorem selectedBoundaryCosts_le (ct cD : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target D N : ℕ, target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → D ≤ cD*Sizes.t n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let W := packedHaloCommonWidth p (haloInverseRingLog s (Sizes.t n i)) s u (target+1) 2
      boundaryControlTimeBound p D s ≤ Sizes.T n ∧
      boundaryControlStockBound p D s ≤ Sizes.T n ∧
      boundaryPublicationTimeBound N D s W ≤ Sizes.T n+(1335*(1032+8*ct))*(N*s*p) ∧
      boundaryPublicationStockBound N D s W ≤ Sizes.T n+(5597*(1032+8*ct))*(N*s*p) := by
  let cW := 1032+8*ct
  let Ktime := 1536*(cD+4)^2+384*cD+1463
  let Kstock := 4608*(cD+4)^2+962*cD+3917
  let KpubTime := 1536*(cD+4)^2+350*cD+1335*cW+104
  let KpubStock := 6656*(cD+4)^2+1426*cD+5597*cW+134
  filter_upwards [selectedAxisPolynomial_le_volume Ktime 0 2,
    selectedAxisPolynomial_le_volume Kstock 0 2,
    selectedAxisPolynomial_le_volume KpubTime 0 2,
    selectedAxisPolynomial_le_volume KpubStock 0 2] with n ht hs hpt hps
  intro h i _ u target D N htarget hband hD
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let W := packedHaloCommonWidth p (haloInverseRingLog s t) s u (target+1) 2
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hW : W ≤ cW*p := selectedPackedHaloCommonWidth_le ct h i u target htarget hband
  obtain ⟨htime,hstock,hpubTime,hpubStock⟩ := boundaryScalarCosts_le hp
    (selectedPrecision_le_axis h i) (h.good.lt i).le hD hW
  have htimeV : Ktime*t^2 ≤ Sizes.T n := by simpa only [pow_zero,mul_one] using ht i
  have hstockV : Kstock*t^2 ≤ Sizes.T n := by simpa only [pow_zero,mul_one] using hs i
  have hpubTimeV : KpubTime*t^2 ≤ Sizes.T n := by simpa only [pow_zero,mul_one] using hpt i
  have hpubStockV : KpubStock*t^2 ≤ Sizes.T n := by simpa only [pow_zero,mul_one] using hps i
  have hscalarTime := hpubTime.trans hpubTimeV
  have hscalarStock := hpubStock.trans hpubStockV
  refine ⟨htime.trans htimeV,hstock.trans hstockV,?_,?_⟩
  · have htraffic := Nat.mul_le_mul_left (1335*N*s) hW
    unfold boundaryPublicationTimeBound
    dsimp only [p,s,t,W,cW] at hscalarTime htraffic ⊢
    nlinarith only [hscalarTime,htraffic]
  · have htraffic := Nat.mul_le_mul_left (5597*N*s) hW
    unfold boundaryPublicationStockBound
    dsimp only [p,s,t,W,cW] at hscalarStock htraffic ⊢
    nlinarith only [hscalarStock,htraffic]

/-- Canonical counter width discharges the format hypothesis from root volume;
only the ordinary data-format and loaded-volume bounds remain. -/
theorem selectedBoundaryCosts_of_volume_le (ct cFormat : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target B x N : ℕ, target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      B ≤ cFormat*Sizes.p n → x ≤ Sizes.T n →
      let p := Sizes.p n
      let s := Sizes.s n i
      let D := max B (Nat.size x)
      let W := packedHaloCommonWidth p (haloInverseRingLog s (Sizes.t n i)) s u (target+1) 2
      boundaryControlTimeBound p D s ≤ Sizes.T n ∧
      boundaryControlStockBound p D s ≤ Sizes.T n ∧
      boundaryPublicationTimeBound N D s W ≤ Sizes.T n+(1335*(1032+8*ct))*(N*s*p) ∧
      boundaryPublicationStockBound N D s W ≤ Sizes.T n+(5597*(1032+8*ct))*(N*s*p) := by
  filter_upwards [selectedBoundaryCosts_le ct (cFormat+1)] with n hn
  intro h i _ u target B x N htarget hband hB hx
  exact hn h i u target (max B (Nat.size x)) N htarget hband
    (selectedDimensionWidth_le_axis cFormat h i hB hx)

end IntegerMultBounds.MathlibTM2.Cost
