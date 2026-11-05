module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBoundaryCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSharedPreparationCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSharedBoundaryVolume

/-! Shared initialization and final erasure use the same selected scalar profile
as boundary completion. Each setup charge is paid once; replicas stay linear. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedSharedPreparationAllowance_le (ct cD : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ D N : ℕ, D ≤ cD*Sizes.p n →
      sharedPreparationAllowance ct (Sizes.T n) (Sizes.p n) (Sizes.s n i) (Sizes.t n i) D N ≤
        2*Sizes.T n+(60*(1032+8*ct)+4*cD+14)*(N*Sizes.s n i*Sizes.p n) := by
  filter_upwards [selectedAxisPolynomial_le_volume (gatherPreparationScalarFactor ct*(cD+1)) 1 1] with n hn
  intro h i _ D N hD
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hs : 1 ≤ s := NeZero.one_le
  have hdimension : D+p ≤ (cD+1)*p := by nlinarith only [hD]
  have hscalar := Nat.mul_le_mul_left (gatherPreparationScalarFactor ct*t) hdimension
  have hscalarV : gatherPreparationScalarFactor ct*(cD+1)*t*p ≤ Sizes.T n := by
    simpa only [pow_one] using hn i
  have hcounter : 4*D+14 ≤ (4*cD+14)*p := by nlinarith only [hD,hp]
  have hn := Nat.mul_le_mul_left N hcounter
  have hreplicas : N*p ≤ N*s*p := Nat.mul_le_mul_right p (Nat.le_mul_of_pos_right N hs)
  have htraffic := Nat.mul_le_mul_left (4*cD+14) hreplicas
  unfold sharedPreparationAllowance
  dsimp only [p,s,t] at hscalar hscalarV hn htraffic ⊢
  nlinarith only [hscalar,hscalarV,hn,htraffic]

private theorem retireAllowance_le {p s t D B W N Vg Vr cD cB cW : ℕ}
    (hp : 1 ≤ p) (hs : 1 ≤ s) (ht : 1 ≤ t) (hst : s ≤ t)
    (hD : D ≤ cD*p) (hB : B ≤ cB*p) (hW : W ≤ cW*p) (hVg : Vg ≤ D) (hVr : Vr ≤ D) :
    sharedBoundaryRetireAllowance W N s D B Vg Vr ≤
      (2*headerCount*(2*cW+3*cD+cB)+2*headerCount+3)*t*p+
        (2*headerCount+2*cW)*(N*s*p) := by
  have hpA : p ≤ t*p := Nat.le_mul_of_pos_left p ht
  have hDA := hD.trans (Nat.mul_le_mul_left cD hpA)
  have hBA := hB.trans (Nat.mul_le_mul_left cB hpA)
  have hWA := hW.trans (Nat.mul_le_mul_left cW hpA)
  have hsWA := Nat.mul_le_mul hst hW
  have hVgA := hVg.trans hDA
  have hVrA := hVr.trans hDA
  have hscalar : W+s*W+D+B+Vg+Vr ≤ (2*cW+3*cD+cB)*(t*p) := by
    nlinarith only [hDA,hBA,hWA,hsWA,hVgA,hVrA]
  have hscaled := Nat.mul_le_mul_left (2*headerCount) hscalar
  have hone : 1 ≤ t*p := hp.trans hpA
  have hfixed := Nat.mul_le_mul_left (2*headerCount+3) hone
  have hN : N ≤ N*s*p :=
    (Nat.le_mul_of_pos_right N hs).trans (Nat.le_mul_of_pos_right _ hp)
  have hNscaled := Nat.mul_le_mul_left (2*headerCount) hN
  have hpay := Nat.mul_le_mul_left (N*s) hW
  unfold sharedBoundaryRetireAllowance
  nlinarith only [hscaled,hfixed,hNscaled,hpay]

theorem selectedSharedBoundaryRetireAllowance_le (ct cD : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target D N Vg Vr : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      D ≤ cD*Sizes.p n → Vg ≤ D → Vr ≤ D →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      sharedBoundaryRetireAllowance (packedHaloCommonWidth p l s u (target+1) 2) N s D
        (inverseCallerWordWidth p u l target s t) Vg Vr ≤
        Sizes.T n+(2*headerCount+2*(1032+8*ct))*(N*s*p) := by
  let cB := 2*(ct+21)+22
  let cW := 1032+8*ct
  let K := 2*headerCount*(2*cW+3*cD+cB)+2*headerCount+3
  filter_upwards [selectedAxisPolynomial_le_volume K 1 1] with n hn
  intro h i _ u target D N Vg Vr hu htarget hband hD hVg hVr
  dsimp only
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hpt := selectedPrecision_le_axis h i
  have hb := retireAllowance_le (N := N) hp NeZero.one_le (hp.trans hpt) (h.good.lt i).le hD
    (selectedInverseCallerWordWidth_le ct h i hu htarget hband)
    (selectedPackedHaloCommonWidth_le ct h i u target htarget hband) hVg hVr
  have hv : K*Sizes.t n i*Sizes.p n ≤ Sizes.T n := by simpa only [pow_one] using hn i
  exact hb.trans (Nat.add_le_add_right hv _)

/-- One canonical format profile prices initialization, boundary completion and
final erasure. Execution supplies the ordinary loaded-volume and format facts. -/
theorem selectedCallerLifecycleCosts_of_volume_le (ct cFormat : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target formatWidth x N Vg Vr : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      formatWidth ≤ cFormat*Sizes.p n → x ≤ (Sizes.T n)^2 →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let D := max formatWidth (Nat.size x)
      let W := packedHaloCommonWidth p l s u (target+1) 2
      Vg ≤ D → Vr ≤ D →
      sharedPreparationAllowance ct (Sizes.T n) p s t D N ≤
        2*Sizes.T n+(60*(1032+8*ct)+4*(cFormat+1)+14)*(N*s*p) ∧
      sharedBoundaryRetireAllowance W N s D (inverseCallerWordWidth p u l target s t) Vg Vr ≤
        Sizes.T n+(2*headerCount+2*(1032+8*ct))*(N*s*p) ∧
      boundaryControlTimeBound p D s ≤ Sizes.T n ∧
      boundaryControlStockBound p D s ≤ Sizes.T n ∧
      boundaryPublicationTimeBound N D s W ≤ Sizes.T n+(1335*(1032+8*ct))*(N*s*p) ∧
      boundaryPublicationStockBound N D s W ≤ Sizes.T n+(5597*(1032+8*ct))*(N*s*p) := by
  filter_upwards [selectedSharedPreparationAllowance_le ct (cFormat+1),
    selectedSharedBoundaryRetireAllowance_le ct (cFormat+1),
    selectedBoundaryCosts_of_volume_le ct cFormat] with n hprep hretire hboundary
  intro h i _ u target formatWidth x N Vg Vr hu htarget hband hformat hx p s t l D W hVg hVr
  have hD := selectedDimensionWidth_le_precision cFormat h hformat hx
  have hp := hprep h i D N hD
  have hr := hretire h i u target D N Vg Vr hu htarget hband hD hVg hVr
  have hb := hboundary h i u target formatWidth x N htarget hband hformat hx
  exact ⟨hp,hr,hb⟩

end IntegerMultBounds.MathlibTM2.Cost
