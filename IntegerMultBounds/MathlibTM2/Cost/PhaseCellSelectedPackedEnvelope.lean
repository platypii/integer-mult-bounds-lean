module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedPassEnvelope
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryHaloRecoveryPrecision
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedBoundaryWidths
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeometryControlSizing

/-! Construct the packed pass envelope from actual selected sizing facts.
Only the format and caller workspace widths remain explicit inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedPackedHaloPassEnvelope (cw cv : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target rhsExp a b V : ℕ)
    (hu : u ≤ Sizes.p n) (hab : a ≤ b) (hb : b ≤ Sizes.s n i)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i)
    (hwidth : executionWidth (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target rhsExp ≤ cw*Sizes.p n)
    (hV : V ≤ cv*Sizes.p n) :
    PackedHaloPassEnvelope (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (Sizes.s n i) (Sizes.t n i) u target rhsExp a b V
      ((2^15+2*cw+cv+426100)*Sizes.t n i*Sizes.p n) := by
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let C := 2^15+2*cw+cv+426100
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have ht : 1 ≤ t := by omega
  have hparam (x c : ℕ) (hx : x ≤ c*p) (hc : c ≤ C) : x ≤ C*t*p := by
    exact hx.trans (Nat.mul_le_mul_right p (hc.trans (Nat.le_mul_of_pos_right C ht)))
  have hthree : 3 ≤ C := by dsimp only [C]; omega
  have htimes := (Nat.mul_le_mul_right t hthree).trans (Nat.le_mul_of_pos_right (C*t) hp)
  have htZ : t+2 ≤ C*t*p := by omega
  have hqw : q ≤ w := by dsimp only [q,w,executionPrecision,executionWidth]; omega
  have hstage : executionStagePrecision p l target rhsExp+1 ≤ w := by
    dsimp only [w,executionWidth,executionStagePrecision]; omega
  have hl := (haloInverseRingLog_bounds hp hst (h.quarter_p_le_theta i)).1
  have hfamily := selectedWeightWorkspaceWidth_le cw h i q w u hwidth hqw hu
  apply PackedHaloPassEnvelope.of_bounds hst hab hb htZ
  · exact hparam _ (2^15) le_rfl (by dsimp only [C]; omega)
  · exact hparam _ cw (hstage.trans hwidth) (by dsimp only [C]; omega)
  · exact hparam _ cw (hqw.trans hwidth) (by dsimp only [C]; omega)
  · exact hparam _ 20 hl (by dsimp only [C]; omega)
  · exact hparam _ 1 (by simpa only [one_mul] using hu) (by dsimp only [C]; omega)
  · exact hparam _ cw hwidth (by dsimp only [C]; omega)
  · exact hband.trans (hst.le.trans (by omega))
  · exact hparam _ cv hV (by dsimp only [C]; omega)
  · exact hparam _ (2*cw+426009) hfamily (by dsimp only [C]; omega)

/-- Both executed precisions satisfy the selected envelope: recovery retains
exactly the initial format. -/
theorem selectedPackedPreparedPassEnvelopes (ct cv : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target a b V : ℕ)
    (hu : u ≤ Sizes.p n) (htarget : target ≤ ct*Sizes.p n) (hab : a ≤ b) (hb : b ≤ Sizes.s n i)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) (hV : V ≤ cv*Sizes.p n) :
    let p := Sizes.p n
    let s := Sizes.s n i
    let t := Sizes.t n i
    let l := haloInverseRingLog s t
    let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
    let boundaryTarget := boundaryRecoveryTarget p (target+1)
    let stage := initialSchurTarget p u (boundaryTableBits p boundaryTarget 2 N) 2
    let k := boundaryHaloRecoveryTarget p boundaryTarget N
    let e := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
    let Z := (2^15+2*(1032+8*ct)+cv+426100)*t*p
    PackedHaloPassEnvelope p l s t u stage 2 a b V Z ∧
      PackedHaloPassEnvelope p l s t u k e a b V Z := by
  dsimp only
  have hw := selectedInverseWorkingWidth_le ct h i u target a b htarget hband
  have hsizing := boundaryHaloRecoveryTarget_sizing (Sizes.p n) u
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2
    (haloBoundary (Sizes.s n i) (Sizes.t n i) (PhaseCellBand.width (Sizes.p n) u) a b).card
  constructor
  · exact selectedPackedHaloPassEnvelope (1032+8*ct) cv h i u _ 2 a b V hu hab hb hband hw hV
  · apply selectedPackedHaloPassEnvelope (1032+8*ct) cv h i u _ _ a b V hu hab hb hband _ hV
    rw [← hsizing.2.2]
    exact hw

end IntegerMultBounds.MathlibTM2.Cost
