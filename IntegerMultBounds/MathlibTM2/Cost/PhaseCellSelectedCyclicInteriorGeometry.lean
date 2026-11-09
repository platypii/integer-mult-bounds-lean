module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicWorkingWidth
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInteriorGeometryEnvelope

/-! Either physical piece uses the same joint cyclic precision. Its geometry
cost is uniform in both the principal window and the piece endpoints. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedCyclicInteriorGeometry_fast_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ u target a span x y : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → x ≤ Sizes.s n i → y ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let N := (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a span).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      (familyHaloInteriorGeometryCost p l s t u (initialSchurTarget p u bits 2) 2 x y : ℝ) ≤
        C*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := selectedInteriorGeometry_width_fast_le (1032+8*ct)
  refine ⟨C,hC,?_⟩
  filter_upwards [hfast] with n hn
  intro h i _ u target a span x y hu htarget hband hx hy
  dsimp only
  exact hn h i u _ 2 x y
    (selectedCyclicWorkingWidth_le ct h i u target a span htarget hband) hu hband hx hy

end IntegerMultBounds.MathlibTM2.Cost
