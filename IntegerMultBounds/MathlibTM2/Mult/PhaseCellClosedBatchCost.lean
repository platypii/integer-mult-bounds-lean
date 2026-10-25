module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBatchExec

/-! A dimension-only executed time bound. Unary origin loading and numerical
weight initialization remain fully charged; no fast-line estimate is asserted. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN

theorem generatedBatchSetupCost_le (P N q s t u band l L B : ℕ) (lo : ℕ → ℕ)
    (hlo : ∀ i < B, lo i ≤ s) :
    generatedBatchSetupCost P N q s t u band l L B lo ≤
      batchInverseSetupCost P N q s t u band L 0 + L*(6*(2*q+8)+9) + 14*(2*q+8) +
        10*q + 2*N + 2*P + 6*l + 119 +
        B*(weightBatchStepCost P s t u q L s (2*q+8) + 134*(L*(2*q+8)) + 15*L + 116) := by
  have hh := batchWeightSetupCost_le P s t u q L (2*q+8) B lo hlo
  dsimp only [generatedBatchSetupCost, batchWeightedSetupCost, prepareBatchRuntimeCost,
    swapBatchPayloadCost, installBatchHeadersCost]
  rw [batchInverseSetupCost_affine]
  nlinarith only [hh]

/-- The complete dimension-only ledger, including final publication and release. -/
def sizedClosedBatchBound (p l B L s t u target rhsExp : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let P := 2^15*p
  let band := PhaseCellBand.width p u
  batchInverseSetupCost P (j+1) q s t u band L 0 + L*(6*(2*q+8)+9) + 14*(2*q+8) +
    10*q + 2*(j+1) + 2*P + 6*l + 119 +
    B*(weightBatchStepCost P s t u q L s (2*q+8) + 134*(L*(2*q+8)) + 15*L + 116) +
    stagePayloadCost B L w + cellArithmeticCost q (inputExponent p cExp) cExp (8*p+1) l w B L +
    publishFromDimensionsCost B L w + releaseBatchRuntimeCost B L q l

theorem sizedClosedBatchCost_le_bound (p l B L s t u target rhsExp : ℕ) (lo : ℕ → ℕ)
    (hlo : ∀ i < B, lo i ≤ s) :
    sizedClosedBatchCost p l B L s t u target rhsExp lo ≤ sizedClosedBatchBound p l B L s t u target rhsExp := by
  have hh := generatedBatchSetupCost_le (2^15*p) (executionStagePrecision p l target rhsExp+1)
    (executionPrecision p l target rhsExp) s t u (PhaseCellBand.width p u) l L B lo hlo
  dsimp only [sizedClosedBatchCost, sizedClosedBatchBound]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
