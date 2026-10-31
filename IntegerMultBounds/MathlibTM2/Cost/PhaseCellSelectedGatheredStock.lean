module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGatheredNumericalStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeometryControlSizing
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloRingSizing

/-! Derive the complete gathered solver's control-width hypothesis from selected
axis metadata and linear target/RHS precision, rather than a workspace oracle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- Precision choices, rather than a supplied word width, determine the native bill. -/
theorem executionWidth_le_linear (cl ct ce p l target rhsExp : ℕ) (hp : 1 ≤ p)
    (hl : l ≤ cl*p) (ht : target ≤ ct*p) (he : rhsExp ≤ ce*p) :
    executionWidth p l target rhsExp ≤ (16*cl+8*ct+8*ce+128)*p := by
  unfold executionWidth executionExponent inputExponent sourceExponent
  nlinarith only [hp,hl,ht,he]

theorem selectedGatheredWidths (cl ct ce : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) (l u target rhsExp : ℕ)
    (hl : l ≤ cl*Sizes.p n) (hu : u ≤ Sizes.p n)
    (ht : target ≤ ct*Sizes.p n) (he : rhsExp ≤ ce*Sizes.p n) :
    let cw := 16*cl+8*ct+8*ce+128
    let q := executionPrecision (Sizes.p n) l target rhsExp
    let w := executionWidth (Sizes.p n) l target rhsExp
    w ≤ cw*Sizes.p n ∧ weightWorkspaceWidth (2^15*Sizes.p n) q w (Sizes.t n i) u ≤
      (2*cw+426009)*w := by
  dsimp only
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hw := executionWidth_le_linear cl ct ce (Sizes.p n) l target rhsExp hp hl ht he
  have hq : executionPrecision (Sizes.p n) l target rhsExp ≤
      executionWidth (Sizes.p n) l target rhsExp := by
    unfold executionPrecision executionWidth
    omega
  have hpw : Sizes.p n ≤ executionWidth (Sizes.p n) l target rhsExp := by
    unfold executionWidth executionExponent inputExponent sourceExponent
    omega
  exact ⟨hw,(selectedWeightWorkspaceWidth_le _ h i _ _ u hw hq hu).trans
    (Nat.mul_le_mul_left _ hpw)⟩

/-- The actual ambient-gap ring choice supplies the remaining logarithm bound. -/
theorem selectedHaloGatheredWidths (ct ce : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target rhsExp : ℕ)
    (hu : u ≤ Sizes.p n) (ht : target ≤ ct*Sizes.p n) (he : rhsExp ≤ ce*Sizes.p n) :
    let l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)
    let cw := 16*20+8*ct+8*ce+128
    let w := executionWidth (Sizes.p n) l target rhsExp
    l ≤ 20*Sizes.p n ∧ 2^l ≤ 20*Sizes.p n ∧ w ≤ cw*Sizes.p n ∧
      weightWorkspaceWidth (2^15*Sizes.p n) (executionPrecision (Sizes.p n) l target rhsExp)
        w (Sizes.t n i) u ≤ (2*cw+426009)*w := by
  dsimp only
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  obtain ⟨hl,hr⟩ := haloInverseRingLog_bounds hp (h.good.lt i) (h.quarter_p_le_theta i)
  obtain ⟨hw,hv⟩ := selectedGatheredWidths 20 ct ce h i _ u target rhsExp hl hu ht he
  exact ⟨hl,hr,hw,hv⟩

/-- The selected near-one axes also satisfy the local padding theorem's gap premise. -/
theorem selectedAxis_gap_le_source {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n)) :
    Sizes.t n i-Sizes.s n i ≤ Sizes.s n i := by
  have hd := h.one_le_d
  have haxis := (h.good.bounds i).lower
  have htarget : Sizes.t n i < 2*Sizes.s n i := by
    by_contra hc
    have ht : 2*Sizes.s n i ≤ Sizes.t n i := by omega
    have hm := Nat.mul_le_mul_left (Sizes.d n) ht
    have hdT := Nat.mul_le_mul_right (Sizes.t n i) hd
    nlinarith only [haxis,hm,hdT]
  omega

/-- Discharge the complete interior stock comparison at selected metadata widths. -/
theorem selectedGatheredInteriorWorkspace_le_linear {Q A : ℕ} {U : Type}
    (hQ : SS.states ≤ Q) (R K cl ct ce : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) (l N B V span L u target rhsExp : ℕ)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hl : l ≤ cl*Sizes.p n) (hu : u ≤ Sizes.p n)
    (ht : target ≤ ct*Sizes.p n) (he : rhsExp ≤ ce*Sizes.p n) :
    let cV := 2*(16*cl+8*ct+8*ce+128)+426009
    gatheredInteriorWorkspace (A := A) (U := U) hQ R K (Sizes.p n) l N B V span L
      (Sizes.s n i) (Sizes.t n i) u target rhsExp ≤
    gatheredInteriorLinearWorkspace (A := A) (U := U) hQ R K (Sizes.p n) l N B V span L
      (Sizes.s n i) (Sizes.t n i) u target rhsExp cV := by
  exact gatheredInteriorWorkspace_le_linear hQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB hL
    (selectedGatheredWidths cl ct ce h i l u target rhsExp hl hu ht he).2

end IntegerMultBounds.MathlibTM2.Cost
