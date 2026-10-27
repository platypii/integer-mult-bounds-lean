module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedClosedBatchExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchCostAffine

/-! The repeated cached interior ledger has no coefficient or exponential weight generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

def cachedBatchCoordinateCost (p l target rhsExp : ℕ) : ℕ :=
  let w := executionWidth p l target rhsExp
  3*rmulCost w+835*w+4*(inputExponent p (sourceExponent l target rhsExp)+2*l+2)+433

def cachedBatchCellCost (p l target rhsExp : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  704+4*rpRecBound q l w+248*(2^l*w)

theorem cachedClosedBatchCost_eq (p l B L s t u target rhsExp : ℕ) :
    cachedClosedBatchCost p l B L s t u target rhsExp =
      cachedClosedBatchCost p l 0 L s t u target rhsExp+
        (B*L)*cachedBatchCoordinateCost p l target rhsExp+
        B*cachedBatchCellCost p l target rhsExp := by
  have hw : 2*executionPrecision p l target rhsExp+8 = executionWidth p l target rhsExp := by
    unfold executionPrecision executionWidth
    omega
  dsimp only [cachedClosedBatchCost,cachedGeneratedBatchSetupCost,cachedBatchWeightedSetupCost,
    preparedBatchWeightedSetupCost,cachedBatchCoordinateCost,cachedBatchCellCost]
  rw [batchInverseSetupCost_affine (2^15*p) (executionStagePrecision p l target rhsExp+1)
    (executionPrecision p l target rhsExp) s t u (PhaseCellBand.width p u) L B]
  simp only [prepareBatchRuntimeCost,swapBatchPayloadCost,installBatchHeadersCost,
    stagePayloadCost,fetchPageCost,cellArithmeticCost,inputStageCost,closedWeightsCost,installInputCost,interiorProductsCost,
    compactPairCost,Fixed.cost,pairFinishCost,fixedMergeCost,fetchScalarCost,
    preparedOutputCost,fetchOutputTableCost,outputFromHeadersCost,closedOutputWeightsCost,
    publishFromDimensionsCost,releaseBatchRuntimeCost,releaseRuntimePagesCost,
    runWeightsCost,runCost,routeWeightsCost,routeCost,scaleOutputPrefixCost,
    swapCellPayloadCost,releaseGeneratorPageCost,releaseWeightPageCost,hw]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
