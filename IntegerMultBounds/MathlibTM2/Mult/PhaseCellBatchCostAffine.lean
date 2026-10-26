module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBatchCost

/-! The executed batch ledger pays construction once and is affine in the
number of cells. All arithmetic, padded products and cleanup are included. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

/-- Repeated arithmetic and weight generation paid per interior coordinate. -/
def batchCoordinateCost (p l t u target rhsExp : ℕ) : ℕ :=
  let P := 2^15*p
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let V := weightWorkspaceWidth P q w t u
  (310*P+124)*tblC V w + 3*rmulCost w + 927*w +
    4*(inputExponent p (sourceExponent l target rhsExp)+2*l+2)+478

/-- Padded convolution and binary-origin work paid per cell, not per coordinate. -/
def batchCellCost (p l t u target rhsExp : ℕ) : ℕ :=
  let P := 2^15*p
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let V := weightWorkspaceWidth P q w t u
  3*tblC V w+8*V+808+4*rpRecBound q l w+248*(2^l*w)

/-- Shared setup is paid exactly once; repeated work separates cell and coordinate counts. -/
theorem sizedClosedBatchBound_eq (p l B L s t u target rhsExp : ℕ) :
    sizedClosedBatchBound p l B L s t u target rhsExp =
      sizedClosedBatchBound p l 0 L s t u target rhsExp +
        (B*L)*batchCoordinateCost p l t u target rhsExp +
        B*batchCellCost p l t u target rhsExp := by
  have hw : 2*executionPrecision p l target rhsExp+8 = executionWidth p l target rhsExp := by
    unfold executionPrecision executionWidth
    omega
  simp only [sizedClosedBatchBound,batchCoordinateCost,batchCellCost,
    retainedWeightStepCost,retainedWeightPageCost,retainedWeightRowsCost,pairLayoutCost,stagePayloadCost,fetchPageCost,cellArithmeticCost,
    inputStageCost,closedWeightsCost,installInputCost,interiorProductsCost,
    compactPairCost,Fixed.cost,pairFinishCost,fixedMergeCost,fetchScalarCost,
    preparedOutputCost,fetchOutputTableCost,outputFromHeadersCost,closedOutputWeightsCost,
    publishFromDimensionsCost,releaseBatchRuntimeCost,releaseRuntimePagesCost,
    runWeightsCost,runCost,routeWeightsCost,routeCost,scaleOutputPrefixCost,
    swapCellPayloadCost,releaseGeneratorPageCost,releaseWeightPageCost]
  simp only [hw]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
