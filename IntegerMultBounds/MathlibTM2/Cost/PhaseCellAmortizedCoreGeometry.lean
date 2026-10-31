module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreGeometry

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

end IntegerMultBounds.MathlibTM2.Cost
