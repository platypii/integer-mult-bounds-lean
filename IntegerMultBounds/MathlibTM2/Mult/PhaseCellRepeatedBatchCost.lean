module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatedClosedBatchExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchCostAffine

/-! Equal-key numerical construction is outside the repeated-work coefficients.
Replica arithmetic pays real multiplications, padded products and linear word
transport; the table exponential evaluator appears only in the shared setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

def repeatedBatchCoordinateCost (p l target rhsExp : ℕ) : ℕ :=
  let w := executionWidth p l target rhsExp
  3*rmulCost w+885*w+4*(inputExponent p (sourceExponent l target rhsExp)+2*l+2)+433

def repeatedBatchCellCost (p l target rhsExp : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  4*rpRecBound q l w+248*(2^l*w)+781

/-- The exact ledger includes generation, replica execution, publication and release. -/
theorem repeatedClosedBatchCost_eq (p l B L s t u target rhsExp lo : ℕ) :
    repeatedClosedBatchCost p l B L s t u target rhsExp lo =
      repeatedClosedBatchCost p l 0 L s t u target rhsExp lo+
        (B*L)*repeatedBatchCoordinateCost p l target rhsExp+
        B*repeatedBatchCellCost p l target rhsExp := by
  have hw : 2*executionPrecision p l target rhsExp+8 = executionWidth p l target rhsExp := by
    unfold executionPrecision executionWidth
    omega
  simp only [repeatedClosedBatchCost,repeatedBatchCoordinateCost,repeatedBatchCellCost,
    stagePayloadCost,fetchPageCost,cellArithmeticCost,inputStageCost,closedWeightsCost,
    installInputCost,interiorProductsCost,compactPairCost,Fixed.cost,pairFinishCost,
    fixedMergeCost,fetchScalarCost,preparedOutputCost,fetchOutputTableCost,
    outputFromHeadersCost,closedOutputWeightsCost,publishFromDimensionsCost,
    releaseBatchRuntimeCost,releaseRuntimePagesCost,runWeightsCost,runCost,
    routeWeightsCost,routeCost,scaleOutputPrefixCost,swapCellPayloadCost,
    releaseGeneratorPageCost,releaseWeightPageCost]
  rw [repeatedGeneratedBatchSetupCost_affine]
  simp only [hw]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
