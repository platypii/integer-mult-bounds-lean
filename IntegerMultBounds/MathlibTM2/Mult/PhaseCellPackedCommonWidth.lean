module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedParameterBounds

/-! One ambient cardinality bound gives every proper job the same packet width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem boundaryHaloTarget_mono_rows (p u target rhsExp : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    boundaryHaloTarget p u target rhsExp N ≤ boundaryHaloTarget p u target rhsExp M := by
  have hsize := Nat.size_le_size hNM
  simp only [boundaryHaloTarget,initialSchurTarget,recoveryFirstTarget_canonical,
    recoveryTarget,boundaryTableBits]
  omega

noncomputable def packedHaloCommonWidth (p l s u target rhsExp : ℕ) : ℕ :=
  executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp s) rhsExp

theorem packedHaloCommonWidth_fits (p l s t u target rhsExp a b : ℕ) [NeZero s] :
    2*packedHaloPrecision p l s t u target rhsExp a b+8 ≤ packedHaloCommonWidth p l s u target rhsExp := by
  have hN : (haloBoundary s t (PhaseCellBand.width p u) a b).card ≤ s := by
    simpa using (haloBoundary s t (PhaseCellBand.width p u) a b).card_le_univ
  have hj := boundaryHaloTarget_mono_rows p u (boundaryRecoveryTarget p target) rhsExp hN
  dsimp [packedHaloPrecision,packedHaloCommonWidth,executionWidth,executionPrecision,
    executionExponent,inputExponent,sourceExponent]
  omega
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
