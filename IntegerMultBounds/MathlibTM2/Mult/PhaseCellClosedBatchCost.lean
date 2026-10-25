module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBatchExec

/-! An origin-independent executed time ledger. Geometry and transcendental
initialization are paid once; binary origin loading is paid at every row.
The required amortized fast-line estimate remains a separate obligation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN

theorem generatedBatchSetupCost_eq (P N q s t u band l L B : ℕ) :
    generatedBatchSetupCost P N q s t u band l L B =
      sharedWeightInitCost P s t u q L (2*q+8) + batchInverseSetupCost P N q s t u band L 0 +
        L*(6*(2*q+8)+9) + 128*weightWorkspaceWidth P q (2*q+8) t u + 14*(2*q+8) +
        10*q + 2*N + 2*P + 6*l + 251 +
        B*(retainedWeightStepCost (weightWorkspaceWidth P q (2*q+8) t u) (2*q+8) P L +
          134*(L*(2*q+8)) + 15*L + 118) := by
  dsimp only [generatedBatchSetupCost, batchWeightedSetupCost, sharedBatchWeightSetupCost,
    prepareBatchRuntimeCost, swapBatchPayloadCost, installBatchHeadersCost]
  rw [batchInverseSetupCost_affine]
  ring

/-- The full ledger with shared initialization and explicit per-row work. -/
def sizedClosedBatchBound (p l B L s t u target rhsExp : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let P := 2^15*p
  let band := PhaseCellBand.width p u
  sharedWeightInitCost P s t u q L (2*q+8) + batchInverseSetupCost P (j+1) q s t u band L 0 +
    L*(6*(2*q+8)+9) + 128*weightWorkspaceWidth P q (2*q+8) t u + 14*(2*q+8) +
    10*q + 2*(j+1) + 2*P + 6*l + 251 +
    B*(retainedWeightStepCost (weightWorkspaceWidth P q (2*q+8) t u) (2*q+8) P L +
      134*(L*(2*q+8)) + 15*L + 118) +
    stagePayloadCost B L w + cellArithmeticCost q (inputExponent p cExp) cExp (8*p+1) l w B L +
    publishFromDimensionsCost B L w + releaseBatchRuntimeCost B L q l

theorem sizedClosedBatchCost_le_bound (p l B L s t u target rhsExp : ℕ) :
    sizedClosedBatchCost p l B L s t u target rhsExp ≤ sizedClosedBatchBound p l B L s t u target rhsExp := by
  have hh := generatedBatchSetupCost_eq (2^15*p) (executionStagePrecision p l target rhsExp+1)
    (executionPrecision p l target rhsExp) s t u (PhaseCellBand.width p u) l L B
  dsimp only [sizedClosedBatchCost, sizedClosedBatchBound]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
