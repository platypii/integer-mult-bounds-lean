module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreGeometry
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloRingSizing

/-! Wider exposure cores preserve locality and linear overlap. Their guard
traffic has the manuscript's five-power saving when cores have width p^8. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Geometry is independent of the particular polynomial chosen for core width. -/
theorem selectedPolynomialCoreGeometry (C e : ℕ) (he : 1 ≤ e) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n))
      (width radius u : ℕ), 0 < width → width ≤ C*(Sizes.p n)^e → radius ≤ width →
      3*width+PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i ∧
        ∀ L ∈ coreGatherLengths (Sizes.s n i) width radius,
          L+PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i := by
  filter_upwards [selectedSourceAxis_eventually_polynomial (3*C+17) e] with n hn
  intro h i width radius u hw hwidth hradius
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hpow : Sizes.p n ≤ (Sizes.p n)^e := by
    simpa only [pow_one] using (pow_le_pow_right' hp he)
  have hband : PhaseCellBand.width (Sizes.p n) u ≤ 17*Sizes.p n := by
    have hs := Nat.sqrt_le_self (16*Sizes.p n/u)
    have hd := Nat.div_le_self (16*Sizes.p n) u
    unfold PhaseCellBand.width
    omega
  have hroom : 3*width+PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i := by
    nlinarith only [hwidth,hband,hpow,hn h i]
  refine ⟨hroom,?_⟩
  intro L hL
  have hlen := coreGatherLength_le (Sizes.s n i) width radius L hw hL
  omega

/-- A concrete manuscript-scale candidate; locality still uses its original guard. -/
def amortizedCoreWidth (ct p : ℕ) : ℕ := (816*(ct+5)+18)*p^8

theorem amortizedCoreWidth_bounds (ct p u target : ℕ) (hp : 1 ≤ p) (htarget : target ≤ ct*p) :
    0 < amortizedCoreWidth ct p ∧ p^8 ≤ amortizedCoreWidth ct p ∧
      localityCoreWidth p u target ≤ amortizedCoreWidth ct p := by
  have hc := localityCoreGeometry_poly ct p u target hp htarget
  have hpow : p^3 ≤ p^8 := pow_le_pow_right' hp (by decide)
  have hguard : localityCoreWidth p u target ≤ (816*(ct+5)+17)*p^3 := by omega
  have hscaled := Nat.mul_le_mul_left (816*(ct+5)+17) hpow
  have hone : 1 ≤ p^8 := Nat.one_le_pow _ _ hp
  unfold amortizedCoreWidth
  constructor
  · positivity
  constructor
  · nlinarith
  · nlinarith only [hguard,hscaled,hone]

/-- The existing amortized width meets the numerical caller's preparation
condition, not only its locality guard. -/
theorem amortizedCoreWidth_preparation (ct p u : ℕ) (hp : 1 ≤ p) :
    p^2+(PhaseCellBand.width p u)^2 ≤ amortizedCoreWidth ct p := by
  have hband : PhaseCellBand.width p u ≤ 17*p := by
    have hs := Nat.sqrt_le_self (16*p/u)
    have hd := Nat.div_le_self (16*p) u
    unfold PhaseCellBand.width
    omega
  have hsquare := Nat.pow_le_pow_left hband 2
  have hpower : p^2 ≤ p^8 := pow_le_pow_right' hp (by decide)
  have hscaled := Nat.mul_le_mul_left 290 hpower
  have hcoefficient : 290 ≤ 816*(ct+5)+18 := by omega
  have hwidth := Nat.mul_le_mul_right (p^8) hcoefficient
  unfold amortizedCoreWidth
  nlinarith only [hsquare,hscaled,hwidth]

/-- The selected cell-length lower bound on core width is automatic for the
same concrete amortized width. -/
theorem selectedAmortizedCoreWidth_cell {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n))
    [NeZero (Sizes.s n i)] (ct : ℕ) :
    Sizes.s n i/(Sizes.t n i-Sizes.s n i)+1 ≤ amortizedCoreWidth ct (Sizes.p n) := by
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hcell := phaseGap_cellLength_le hp (h.good.lt i) (h.quarter_p_le_theta i)
  have hsmall : 4*Sizes.p n+1 ≤ (Sizes.p n)^2 := by
    have hh := h.thirteen_le_p
    nlinarith only [hh]
  have hpower : (Sizes.p n)^2 ≤ (Sizes.p n)^8 := pow_le_pow_right' hp (by decide)
  have hwidth : (Sizes.p n)^8 ≤ amortizedCoreWidth ct (Sizes.p n) := by
    unfold amortizedCoreWidth
    exact Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- No more than two line-volumes of core slots, including the short last core. -/
theorem coreSlots_le_two (s width : ℕ) (hw : width ≤ s) :
    (coreIndices s width).length*width ≤ 2*s := by
  have hc : (coreIndices s width).length*width ≤ s+width := by
    simp only [coreIndices,List.length_range]
    exact (Nat.div_mul_le_self (s+width-1) width).trans (Nat.sub_le _ _)
  omega

/-- A p^3 guard per p^8 core loses five powers, independently of line length. -/
theorem coreGuardTraffic_amortized (s width radius p H : ℕ)
    (hw : width ≤ s) (hwidth : p^8 ≤ width) (hradius : radius ≤ H*p^3) :
    (coreIndices s width).length*radius*p^5 ≤ 2*H*s := by
  have hguard : radius*p^5 ≤ H*width := by
    calc
      _ ≤ (H*p^3)*p^5 := Nat.mul_le_mul_right _ hradius
      _ = H*p^8 := by ring
      _ ≤ H*width := Nat.mul_le_mul_left H hwidth
  have hc := coreSlots_le_two s width hw
  calc
    _ = (coreIndices s width).length*(radius*p^5) := by ring
    _ ≤ (coreIndices s width).length*(H*width) := Nat.mul_le_mul_left _ hguard
    _ = H*((coreIndices s width).length*width) := by ring
    _ ≤ H*(2*s) := Nat.mul_le_mul_left H hc
    _ = _ := by ring

/-- Selected axes have room for the wider core and its original locality guard. -/
theorem selectedAmortizedCoreGeometry (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) (u target : ℕ),
      target ≤ ct*Sizes.p n →
      let width := amortizedCoreWidth ct (Sizes.p n)
      let radius := localityCoreWidth (Sizes.p n) u target
      0 < width ∧ (Sizes.p n)^8 ≤ width ∧ radius ≤ width ∧
        3*width+PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i ∧
        ∀ L ∈ coreGatherLengths (Sizes.s n i) width radius,
          L+PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i := by
  filter_upwards [selectedPolynomialCoreGeometry (816*(ct+5)+18) 8 (by decide)] with n hn
  intro h i u target htarget
  dsimp only
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  obtain ⟨hw,hwide,hguard⟩ := amortizedCoreWidth_bounds ct (Sizes.p n) u target hp htarget
  exact ⟨hw,hwide,hguard,hn h i _ _ u hw (by rfl) hguard⟩

/-- The wider cores keep the existing overlap, seam-count and guard-saving contracts. -/
theorem selectedAmortizedCoreHalo (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ (u target : ℕ), target ≤ ct*Sizes.p n →
      let width := amortizedCoreWidth ct (Sizes.p n)
      let radius := localityCoreWidth (Sizes.p n) u target
      (∑ k ∈ (coreIndices (Sizes.s n i) width).toFinset,
        (coreHalo (Sizes.s n i) width k (PhaseCellBand.width (Sizes.p n) u)
          (localityDepth (Sizes.p n) target)).card) ≤ 9*Sizes.s n i ∧
      (((coreIndices (Sizes.s n i) width).toFinset).filter (fun k =>
        ¬ (radius ≤ coreStart width k ∧
          coreStart width k+coreLength (Sizes.s n i) width k+radius ≤ Sizes.s n i))).card ≤ 3 ∧
      (coreIndices (Sizes.s n i) width).length*radius*(Sizes.p n)^5 ≤
        2*(816*(ct+5)+17)*Sizes.s n i := by
  filter_upwards [selectedAmortizedCoreGeometry ct] with n hn
  intro h i _ u target htarget
  dsimp only
  obtain ⟨hw,hwide,hguard,hroom,hlen⟩ := hn h i u target htarget
  have hwidth : amortizedCoreWidth ct (Sizes.p n) ≤ Sizes.s n i := by omega
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hc := localityCoreGeometry_poly ct (Sizes.p n) u target hp htarget
  exact ⟨coreHalo_volume_le_nine _ _ _ hwidth hguard,
    coreHalo_fallback_count _ _ _ hguard,
    coreGuardTraffic_amortized _ _ _ _ _ hwidth hwide (by omega)⟩

/-- The concrete amortized width discharges all core-geometry hypotheses of
selected numerical class execution. -/
theorem selectedAmortizedCoreCallerGeometry (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
    ∀ [NeZero (Sizes.s n i)], ∀ (u target : ℕ), target ≤ ct*Sizes.p n →
    let width := amortizedCoreWidth ct (Sizes.p n)
    let radius := localityCoreWidth (Sizes.p n) u target
    0 < width ∧ width ≤ Sizes.s n i ∧ radius ≤ width ∧
      Sizes.s n i/(Sizes.t n i-Sizes.s n i)+1 ≤ width ∧
      (Sizes.p n)^2+(PhaseCellBand.width (Sizes.p n) u)^2 ≤ width ∧
      ∀ L ∈ coreGatherLengths (Sizes.s n i) width radius, L ≤ Sizes.s n i := by
  filter_upwards [selectedAmortizedCoreGeometry ct] with n hn
  intro h i _ u target htarget
  dsimp only
  obtain ⟨hw,hwide,hguard,hroom,hlen⟩ := hn h i u target htarget
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  exact ⟨hw,by omega,hguard,selectedAmortizedCoreWidth_cell h i ct,
    amortizedCoreWidth_preparation ct (Sizes.p n) u hp,
    fun L hL => (Nat.le_add_right L _).trans (hlen L hL)⟩

end IntegerMultBounds.MathlibTM2.Cost
