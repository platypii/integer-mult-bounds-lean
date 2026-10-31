module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedNumericalSetup
public import IntegerMultBounds.NLogN.PhaseCellCoreLocalityGeometry

/-! Selected source axes eventually dominate the locality core's polynomial
size. Every generated movement length then has separated boundaries. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix

/-- The selected source axis, as well as its target axis, absorbs fixed precision polynomials. -/
theorem selectedSourceAxis_eventually_polynomial (C e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), C*(Sizes.p n)^e ≤ Sizes.s n i := by
  filter_upwards [selectedAxis_eventually_polynomial (2*C) e] with n hn
  intro h i
  have hd := h.one_le_d
  have haxis := (h.good.bounds i).lower
  have htarget : Sizes.t n i < 2*Sizes.s n i := by
    by_contra hc
    have ht : 2*Sizes.s n i ≤ Sizes.t n i := by omega
    have hm := Nat.mul_le_mul_left (Sizes.d n) ht
    have hdT := Nat.mul_le_mul_right (Sizes.t n i) hd
    nlinarith only [haxis,hm,hdT]
  have hpoly := hn i
  nlinarith only [hpoly,htarget]

/-- Choose core width equal to the locality guard once for the selected class. -/
theorem selectedCoreGeometry (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) (u target : ℕ),
      target ≤ ct*Sizes.p n →
      let width := localityCoreWidth (Sizes.p n) u target
      0 < width ∧ 3*width+PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i ∧
        ∀ L ∈ coreGatherLengths (Sizes.s n i) width width, L+PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i := by
  filter_upwards [selectedSourceAxis_eventually_polynomial (816*(ct+5)+17) 3] with n hn
  intro h i u target htarget
  dsimp only
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hw := localityCoreWidth_pos hp u target
  have hroom := (localityCoreGeometry_poly ct (Sizes.p n) u target hp htarget).trans (hn h i)
  refine ⟨hw,hroom,?_⟩
  intro L hL
  have hlen := coreGatherLength_le (Sizes.s n i) _ _ L hw hL
  omega

/-- The chosen core/guard width also preserves the existing linear overlap bill. -/
theorem selectedCoreHalo_volume_le_nine (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ (u target : ℕ), target ≤ ct*Sizes.p n →
      let width := localityCoreWidth (Sizes.p n) u target
      (∑ k ∈ (coreIndices (Sizes.s n i) width).toFinset,
        (coreHalo (Sizes.s n i) width k (PhaseCellBand.width (Sizes.p n) u)
          (localityDepth (Sizes.p n) target)).card) ≤ 9*Sizes.s n i := by
  filter_upwards [selectedCoreGeometry ct] with n hn
  intro h i _ u target htarget
  dsimp only
  have hroom := (hn h i u target htarget).2.1
  apply coreHalo_volume_le_nine
  · omega
  · exact le_rfl

end IntegerMultBounds.MathlibTM2.Cost
