module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchSetupStock
import Mathlib.Tactic.GCongr

/-! The shared batch setup allowance is monotone in selected cell length. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem generatedBatchSetupWorkspace_zero_mono
    (C P N q s t u band l L M : ℕ) (hL : L ≤ M) :
    generatedBatchSetupWorkspace C P N q s t u band l L 0 ≤
      generatedBatchSetupWorkspace C P N q s t u band l M 0 := by
  have hsize := Nat.size_le_size hL
  unfold generatedBatchSetupWorkspace batchWeightedSetupWorkspace sharedBatchWeightSetupWorkspace
    sharedWeightInitWorkspace retainedWeightStepWorkspace retainedWeightPageWorkspace
    batchInverseSetupWorkspace headerGeneratorSetupWorkspace numericalGeneratorSetupWorkspace
    factorFactoryWorkspace packedGeneratorSetupWorkspace generatorSetupWorkspace
    generatedEncodedColumnWorkspace generatedIntegerColumnWorkspace columnEncodingWorkspace
    prepareIntegerIterationsWorkspace integerIterationWorkspace preparedIntegerStepWorkspace
    consumeIntegerRowWorkspace realWeightWorkspace reversedColumnWorkspace
    coefficientWorkspaceWidth coefficientWidthCost prepareCoefficientHeadersCost
    weightHeadersCost pairLayoutCost prepareBatchRuntimeCost releaseConstructionCost
    prepareBatchGeneratorPageWorkspace prepareBatchGeneratorPageCost packGeneratorsCost
    constructFactorPageCost factorRowStepCost packWeightBatchCost coefficientHeadersLinearCost
    tblC releaseFactorPageCost replicateGeneratorsCost swapBatchPayloadCost
  dsimp only
  gcongr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
