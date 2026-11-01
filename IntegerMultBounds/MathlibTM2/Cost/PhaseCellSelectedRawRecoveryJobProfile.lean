module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedHaloCommonWidth
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatheredStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryJobProfiles

/-! The mathematical constructor with the common packet width supplies all
scalar hypotheses of the selected restoring scheduler. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedRawRecoveryJob_profile (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] {u target a b V : ℕ}
    {α gap : ℝ} {C : ZMod (Sizes.s n i) → GaussianInt}
    (bounds : PackedHaloParameterBounds (p := Sizes.p n)
      (l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (t := Sizes.t n i)
      (u := u) (target := target+1) (rhsExp := 2) (a := a) (b := b) (V := V) α gap C)
    (hu : u ≤ Sizes.p n) (htarget : target ≤ ct*Sizes.p n)
    (Fs : List (ZMod (Sizes.s n i) → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value (Sizes.p n) (F j)‖ ≤ 1) :
    let cH := 1032+8*ct
    let cw := 16*20+8*cH+8*2+128
    let cVratio := 2*cw+426009
    let W := packedHaloCommonWidth (Sizes.p n)
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) u (target+1) 2
    let r := RawRecoveryJob.ofComplexBounds bounds Fs hF W
      (packedHaloCommonWidth_fits _ _ _ _ _ _ _ _ _)
    (r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
      r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
      r.problem.l ≤ 20*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
      2^r.problem.l ≤ 20*r.problem.p ∧ r.problem.metadataWidth ≤ (cVratio*cw)*r.problem.p ∧
      r.W ≤ cH*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1) ∧
    (r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth ∧ r.problem.Fs.length = 2*Fs.length) ∧
    r.problem.target ≤ cH*Sizes.p n := by
  dsimp only
  let cH := 1032+8*ct
  let cw := 16*20+8*cH+8*2+128
  let cVratio := 2*cw+426009
  let W := packedHaloCommonWidth (Sizes.p n)
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) u (target+1) 2
  let r := RawRecoveryJob.ofComplexBounds bounds Fs hF W
    (packedHaloCommonWidth_fits _ _ _ _ _ _ _ _ _)
  obtain ⟨hp,hl,ht,hu',he,_,_,_,hN,hr,hW,_,hH⟩ :=
    RawRecoveryJob.ofComplexBounds_profile bounds Fs hF W
      (packedHaloCommonWidth_fits _ _ _ _ _ _ _ _ _)
  have hHbound := selectedBoundaryHaloTarget_le ct h i u target a b htarget bounds.hband
  have hWbound := selectedPackedHaloCommonWidth_le ct h i u target htarget bounds.hband
  have hp1 : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have heBound : 2 ≤ 2*Sizes.p n := by omega
  obtain ⟨hlBound,hRing,hw,hV⟩ := selectedHaloGatheredWidths cH 2 h i u
    (boundaryHaloTarget (Sizes.p n) u (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2
      (haloBoundary (Sizes.s n i) (Sizes.t n i) (PhaseCellBand.width (Sizes.p n) u) a b).card)
    2 hu hHbound heBound
  have hw' : r.problem.wordWidth ≤ cw*r.problem.p := by
    simpa only [r,ReplicaHaloProblem.wordWidth,hp,hl,hH,he,cw,cH] using hw
  have hV' : r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth := by
    simpa only [r,ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,
      ReplicaHaloProblem.wordWidth,hp,hl,ht,hu',hH,he,cVratio,cw,cH] using hV
  have hVabs := hV'.trans (Nat.mul_le_mul_left cVratio hw')
  change (r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
      r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
      r.problem.l ≤ 20*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
      2^r.problem.l ≤ 20*r.problem.p ∧ r.problem.metadataWidth ≤ (cVratio*cw)*r.problem.p ∧
      r.W ≤ cH*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1) ∧
    (r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth ∧ r.problem.Fs.length = 2*Fs.length) ∧
    r.problem.target ≤ cH*Sizes.p n
  refine ⟨⟨hp,ht,hl,?_,?_,hw',?_,?_,?_,he,?_,?_⟩,⟨hV',hN⟩,?_⟩
  · simpa only [r,hp,hu'] using hu
  · simpa only [r,hp,hl] using hlBound
  · simpa only [r,hp,hl] using hRing
  · simpa only [Nat.mul_assoc] using hVabs
  · simpa only [r,hW,hp,W,cH] using hWbound
  · rw [hr]; omega
  · rw [hr]; omega
  · simpa only [r,hH,cH] using hHbound

end IntegerMultBounds.MathlibTM2.Cost
