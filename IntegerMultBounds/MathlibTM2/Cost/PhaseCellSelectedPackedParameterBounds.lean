module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedParameterBounds
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloRingSizing
public import IntegerMultBounds.MathlibTM2.Mult.Sizes

/-! The selected dimensions discharge packed-factory sizing and phase padding. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- Selected ambient sizes supply phase-gap and ring-fit fields. The remaining
premises are analytic band/operand facts and the proper interval's geometry. -/
theorem selectedPackedHaloParameterBounds {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n))
    [NeZero (Sizes.s n i)] (u target rhsExp a b : ℕ) :
    let p := Sizes.p n
    let s := Sizes.s n i
    let t := Sizes.t n i
    let l := haloInverseRingLog s t
    ∀ (α gap : ℝ) (C : ZMod s → GaussianInt),
      8*p ≤ 2^u → 0 < α → 1 ≤ u → α^2 = (u : ℝ) →
      (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1) → α^2*gap ≤ p →
      PhaseCellBand.width p u ≤ s → a ≤ b → b ≤ s → a < s →
      b-a+PhaseCellBand.width p u ≤ s →
      (∀ k, ‖value (packedHaloPrecision p l s t u target rhsExp a b) (C k)‖ ≤ (2 : ℝ)^rhsExp) →
      SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))) →
      ScalarPlacement.PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
        (target := target) (rhsExp := rhsExp) (a := a) (b := b)
        (V := packedHaloWorkspaceWidth p l s t u target rhsExp a b) α gap C := by
  dsimp only
  intro α gap C hwidth hα hu hαu hgap hbudget hband hab hbs haLt hsep hC hdom
  exact ScalarPlacement.PackedHaloParameterBounds.ofAnalytic (by have := h.thirteen_le_p; omega)
    hwidth hα (h.good.lt i) hu hαu (h.quarter_p_le_theta i) hgap hbudget hband hab hbs haLt
    (haloInverseRingLog_fits _ _ _) hsep hC hdom
end IntegerMultBounds.MathlibTM2.Cost
