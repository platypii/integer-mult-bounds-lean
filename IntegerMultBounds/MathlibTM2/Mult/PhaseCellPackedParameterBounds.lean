module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedFactorySetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedGeometryWidth

/-! Separate analytic packed-factory assumptions from derived machine sizing. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def packedHaloPrecision (p l s t u target rhsExp a b : ℕ) [NeZero s] : ℕ :=
  executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
    (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp

noncomputable def packedHaloWorkspaceWidth (p l s t u target rhsExp a b : ℕ) [NeZero s] : ℕ :=
  let q := packedHaloPrecision p l s t u target rhsExp a b
  weightWorkspaceWidth (2^15*p) q (2*q+8) t u

namespace ScalarPlacement.PackedHaloParameterBounds
variable {p l s t u target rhsExp a b : ℕ} [NeZero s] {α gap : ℝ} {C : ZMod s → GaussianInt}

/-- Analytic interval bounds determine all binary workspace-fit premises. -/
theorem ofAnalytic (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α)
    (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1))
    (hbudget : α^2*gap ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hab : a ≤ b) (hbs : b ≤ s) (haLt : a < s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hsep : b-a+PhaseCellBand.width p u ≤ s)
    (hC : ∀ k, ‖value (packedHaloPrecision p l s t u target rhsExp a b) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ)))) :
    ScalarPlacement.PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
      (target := target) (rhsExp := rhsExp) (a := a) (b := b)
      (V := packedHaloWorkspaceWidth p l s t u target rhsExp a b) α gap C := by
  let q := packedHaloPrecision p l s t u target rhsExp a b
  have hP : 13 ≤ 2^15*p := by omega
  have hfits := weightWorkspaceWidth_packed_fits (P := 2^15*p) (q := q) (w := 2*q+8)
    hP (NeZero.pos s) hst hu hband hab hbs
  have hw : executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp
      (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp = 2*q+8 := by
    dsimp [q,packedHaloPrecision,executionWidth,executionPrecision]
    omega
  exact {
    hp := hp
    hwidth := hwidth
    hα := hα
    hst := hst
    hu := hu
    hαu := hαu
    hθ := hθ
    hgap := hgap
    hbudget := hbudget
    hband := hband
    has := hab.trans hbs
    hbs := hbs
    hpad := hpad
    hfitV := hfits.1
    hab := hab
    haLt := haLt
    hsep := hsep
    hwide := hfits.2.1
    hVeq := rfl
    hwV := hw.symm ▸ hfits.2.2.1
    hcoords := hfits.2.2.2.1
    hunits := hw.symm ▸ hfits.2.2.2.2
    hC := hC
    hdom := hdom }
end ScalarPlacement.PackedHaloParameterBounds
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
