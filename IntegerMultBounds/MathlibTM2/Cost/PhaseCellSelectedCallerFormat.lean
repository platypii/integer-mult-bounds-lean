module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerCanonicalFormat
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCallerLifecycleCost

/-! Choose the actual caller format from its dimensions. Selected widths and
the source-volume bound discharge its canonical scalar/volume profile. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def callerFormatFactor (ct cV cR : ℕ) : ℕ := (2*(ct+21)+22)+cV+cR

theorem selectedCallerFormat_profile (ct cV cR : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target N radius width Vg Vr : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      radius ≤ Sizes.s n i → width ≤ Sizes.s n i →
      Vg ≤ cV*Sizes.p n → Vr ≤ cR*Sizes.p n →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let B := inverseCallerWordWidth p u l target s t
      let W := packedHaloCommonWidth p l s u (target+1) 2
      N ≤ Sizes.T n →
      callerCounterBound p u l target s t B W N radius width ≤ (Sizes.T n)^2 ∧
      callerFormatWidth B Vg Vr ≤ callerFormatFactor ct cV cR*p ∧
      canonicalCallerFormat p u l target s t B W N radius width Vg Vr ≤
        (callerFormatFactor ct cV cR+1)*p := by
  let cB := 2*(ct+21)+22
  let cW := 1032+8*ct
  let K := ct+28+cB+2*cW
  filter_upwards [selectedAxisPolynomial_le_volume K 1 1] with n hn
  intro h i _ u target N radius width Vg Vr hu htarget hband hradius hwidth hVg hVr
    p s t l B W hsource
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hpt : p ≤ t := selectedPrecision_le_axis h i
  have hst : s ≤ t := (h.good.lt i).le
  have hB : B ≤ cB*p := selectedInverseCallerWordWidth_le ct h i hu htarget hband
  have hW : W ≤ cW*p := selectedPackedHaloCommonWidth_le ct h i u target htarget hband
  have hl := (haloInverseRingLog_bounds hp (h.good.lt i) (h.quarter_p_le_theta i)).1
  have hscalar : p+u+l+target+s+t+B+W+3*radius+width ≤ (ct+28+cB+cW)*t := by
    have huT := hu.trans hpt
    have htargetT := htarget.trans (Nat.mul_le_mul_left ct hpt)
    have hlT := hl.trans (Nat.mul_le_mul_left 20 hpt)
    have hBT := hB.trans (Nat.mul_le_mul_left cB hpt)
    have hWT := hW.trans (Nat.mul_le_mul_left cW hpt)
    have hrT := hradius.trans hst
    have hwT := hwidth.trans hst
    nlinarith only [hpt,huT,htargetT,hlT,hBT,hWT,hst,hrT,hwT]
  have hscale := Nat.mul_le_mul_left (ct+28+cB+cW) (Nat.le_mul_of_pos_right t hp)
  have hsw := Nat.mul_le_mul hst hW
  have htotal : p+u+l+target+s+t+B+W+3*radius+width+s*W ≤ K*t*p := by
    dsimp only [K]
    nlinarith only [hscalar,hscale,hsw]
  have hroot : K*t*p ≤ Sizes.T n := by simpa only [pow_one] using hn i
  have hscalarRoot := htotal.trans hroot
  have hsWroot : s*W ≤ Sizes.T n := by omega
  have hsourceSq : N*s*W ≤ (Sizes.T n)^2 := by
    have hv := Nat.mul_le_mul hsource hsWroot
    simpa only [Nat.mul_assoc,pow_two] using hv
  have hx : callerCounterBound p u l target s t B W N radius width ≤ (Sizes.T n)^2 :=
    max_le hsourceSq (hscalarRoot.trans (Nat.le_self_pow (by decide) _))
  have hformat : callerFormatWidth B Vg Vr ≤ callerFormatFactor ct cV cR*p := by
    unfold callerFormatWidth callerFormatFactor
    apply max_le
    · dsimp only [cB] at hB
      nlinarith only [hB]
    · apply max_le <;> nlinarith only [hVg,hVr]
  exact ⟨hx,hformat,selectedDimensionWidth_le_precision _ h hformat hx⟩

/-- The actual canonical caller format supplies both the precision profile and
all retained format inequalities required by lifecycle pricing. -/
theorem selectedCanonicalCallerCosts_le (ct cV cR : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target N radius width Vg Vr : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      radius ≤ Sizes.s n i → width ≤ Sizes.s n i →
      Vg ≤ cV*Sizes.p n → Vr ≤ cR*Sizes.p n →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let B := inverseCallerWordWidth p u l target s t
      let W := packedHaloCommonWidth p l s u (target+1) 2
      let D := canonicalCallerFormat p u l target s t B W N radius width Vg Vr
      N ≤ Sizes.T n →
      sharedPreparationAllowance ct (Sizes.T n) p s t D N ≤
        2*Sizes.T n+(60*(1032+8*ct)+4*(callerFormatFactor ct cV cR+1)+14)*(N*s*p) ∧
      sharedBoundaryRetireAllowance W N s D B Vg Vr ≤
        Sizes.T n+(2*headerCount+2*(1032+8*ct))*(N*s*p) ∧
      boundaryControlTimeBound p D s ≤ Sizes.T n ∧
      boundaryControlStockBound p D s ≤ Sizes.T n ∧
      boundaryPublicationTimeBound N D s W ≤ Sizes.T n+(1335*(1032+8*ct))*(N*s*p) ∧
      boundaryPublicationStockBound N D s W ≤ Sizes.T n+(5597*(1032+8*ct))*(N*s*p) := by
  filter_upwards [selectedCallerFormat_profile ct cV cR,
    selectedCallerLifecycleCosts_of_volume_le ct (callerFormatFactor ct cV cR)] with n hprofile hcost
  intro h i _ u target N radius width Vg Vr hu htarget hband hradius hwidth hVg hVr
    p s t l B W D hsource
  obtain ⟨hx,hformat,_⟩ := hprofile h i u target N radius width Vg Vr hu htarget hband
    hradius hwidth hVg hVr hsource
  have hWpos : 1 ≤ W := by
    dsimp only [W,packedHaloCommonWidth,executionWidth,executionPrecision]
    omega
  have hbits := (canonicalCallerFormat_fits p u l target s t B W N radius width Vg Vr
    (NeZero.one_le) hWpos).2.2.1
  exact hcost h i u target (callerFormatWidth B Vg Vr)
    (callerCounterBound p u l target s t B W N radius width) N Vg Vr hu htarget hband hformat hx
    (by have hv := hbits 1; change Vg ≤ D at hv; exact hv)
    (by have hv := hbits 2; change Vr ≤ D at hv; exact hv)

end IntegerMultBounds.MathlibTM2.Cost
