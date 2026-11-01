module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorInitialization
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCommonWidth

/-! The actual common packet format fits every core halo and is linear in the
selected precision, independently of the halo endpoints. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedPackedHaloCommonWidth_le (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target : ℕ)
    (htarget : target ≤ ct*Sizes.p n)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) :
    packedHaloCommonWidth (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (Sizes.s n i) u (target+1) 2 ≤ (1032+8*ct)*Sizes.p n := by
  have hw := selectedInverseRowWorkingWidth_le ct h i u target (Sizes.s n i) htarget hband le_rfl
  simpa only [packedHaloCommonWidth,(boundaryHaloTarget_sizing _ _ _ _ _ _).2.2] using hw

/-- The constructor's numerical target is bounded by the same common format;
no additional per-job accuracy-bound hypothesis is needed. -/
theorem selectedBoundaryHaloTarget_le (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target a b : ℕ)
    (htarget : target ≤ ct*Sizes.p n)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) :
    boundaryHaloTarget (Sizes.p n) u (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2
      (haloBoundary (Sizes.s n i) (Sizes.t n i) (PhaseCellBand.width (Sizes.p n) u) a b).card ≤
      (1032+8*ct)*Sizes.p n := by
  have hrows : (haloBoundary (Sizes.s n i) (Sizes.t n i)
      (PhaseCellBand.width (Sizes.p n) u) a b).card ≤ Sizes.s n i := by
    simpa using Finset.card_le_univ
      (s := haloBoundary (Sizes.s n i) (Sizes.t n i) (PhaseCellBand.width (Sizes.p n) u) a b)
  have ht := boundaryHaloTarget_mono_rows (Sizes.p n) u
    (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2 hrows
  have hw := selectedPackedHaloCommonWidth_le ct h i u target htarget hband
  have hformat : boundaryHaloTarget (Sizes.p n) u
      (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2 (Sizes.s n i) ≤
      packedHaloCommonWidth (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (Sizes.s n i) u (target+1) 2 := by
    unfold packedHaloCommonWidth executionWidth executionExponent inputExponent sourceExponent
    omega
  exact ht.trans (hformat.trans hw)

end IntegerMultBounds.MathlibTM2.Cost
