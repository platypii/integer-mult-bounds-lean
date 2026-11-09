module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellUncachedInteriorPolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloInteriorCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInteriorGeometryEnvelope

/-! Constructor overhead for any working target. The target may depend on a
joint boundary count; no per-window precision formula is imposed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open IntegerMultBounds.NLogN

theorem solveHaloInteriorCost_weights_poly {s t : ℕ} [NeZero s]
    (p l u target rhsExp a b Z : ℕ) (hst : s < t) (hZ : 1 ≤ Z)
    (hP : 2^15*p ≤ Z) (hN : executionStagePrecision p l target rhsExp+1 ≤ Z)
    (hq : executionPrecision p l target rhsExp ≤ Z) (hl : l ≤ Z) (hu : u ≤ Z)
    (hw : executionWidth p l target rhsExp ≤ Z)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ Z)
    (hkeys : ∀ L ∈ haloLengthCandidates s t (IntegerMultBounds.NLogN.PhaseCellBand.width p u) a b,
      L ≤ Z) :
    solveHaloInteriorCost p l s t u target rhsExp a b ≤
      familyHaloInteriorGeometryCost p l s t u target rhsExp a b+10000000*t*Z^4 := by
  exact (solveHaloInteriorCost_le hst p l u target rhsExp a b).trans
    (haloInteriorCostBound_weights_poly p l u target rhsExp a b Z hst hZ
      hP hN hq hl hu hw hV hkeys)

/-- Actual construction at an arbitrary target: retain setup controls and
quartic weight generation once, with geometry arithmetic priced by axis volume. -/
theorem solveHaloInteriorCost_width_fast_le (cw : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ p target rhsExp s t u a b Z : ℕ, ∀ [NeZero s],
      let l := haloInverseRingLog s t
      let q := executionPrecision p l target rhsExp
      let w := executionWidth p l target rhsExp
      1 ≤ p → s < t → 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 → w ≤ cw*p →
      1 ≤ Z → 2^15*p ≤ Z → executionStagePrecision p l target rhsExp+1 ≤ Z →
      q ≤ Z → l ≤ Z → u ≤ Z → w ≤ Z →
      weightWorkspaceWidth (2^15*p) q w t u ≤ Z →
      (∀ L ∈ haloLengthCandidates s t (PhaseCellBand.width p u) a b, L ≤ Z) →
      (solveHaloInteriorCost p l s t u target rhsExp a b : ℝ) ≤
        (familyHaloControlCost p l s t u target rhsExp a b : ℝ)+
          E*(t : ℝ)*(p : ℝ)^(129/128 : ℝ)+(10000000*t*Z^4 : ℕ) := by
  obtain ⟨E,hE,hfast⟩ := familyInteriorGeometry_ring_fast_le cw
  refine ⟨E,hE,?_⟩
  intro p target rhsExp s t u a b Z _
  dsimp only
  intro hp hst htheta hw hZ hP hN hq hl hu hwZ hV hkeys
  have hc := (Nat.cast_le (α := ℝ)).mpr
    (solveHaloInteriorCost_weights_poly p _ u target rhsExp a b Z hst hZ
      hP hN hq hl hu hwZ hV hkeys)
  have hg := hfast p target rhsExp s t u a b hp hst htheta hw
  push_cast only [Nat.cast_add] at hc
  exact hc.trans (add_le_add hg (le_refl _))

end IntegerMultBounds.MathlibTM2.Cost
