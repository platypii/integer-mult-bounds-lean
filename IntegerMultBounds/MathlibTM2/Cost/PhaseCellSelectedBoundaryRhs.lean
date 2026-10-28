module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedMaskCost

/-! The fully generated mask/scan/fold boundary RHS pipeline costs O(t*p). -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem generatedBoundaryRhs_selected_fast_le (cw : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)) (band a b w : ℕ),
      band ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i → w ≤ cw*Sizes.p n →
      generatedBoundaryRhsCost (Sizes.s n i) (Sizes.t n i) band a b w ≤
        C*Sizes.t n i*Sizes.p n := by
  obtain ⟨K,hK⟩ := selectedMasks_fast_le
  refine ⟨K+600*(cw+1),?_⟩
  intro n h i band a b w hband ha hb hw
  have hm := hK n h i band a b hband ha hb
  have hst : Sizes.s n i+1 ≤ Sizes.t n i := h.good.lt i
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hw' : w+1 ≤ (cw+1)*Sizes.p n := by nlinarith only [hw,hp]
  have hv := Nat.mul_le_mul hst hw'
  dsimp only [generatedBoundaryRhsCost]
  nlinarith only [hm,hv]

end IntegerMultBounds.MathlibTM2.Cost
