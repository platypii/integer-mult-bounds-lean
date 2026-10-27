module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingRows

/-! Separate actual coefficient generation, row arithmetic, mask setup and stream work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem spatialCouplingRowsCost_eq (P q w s t u band a b : ℕ) :
    spatialCouplingRowsCost P q w s t u band a b =
      prepareCouplingGuardCost s t band a b+buildMarkedRowCoefficientPacketCost P q w s t u band 0+
      s*markedRowCoefficientCost P q (liftedCoefficientWidth P q w s t u band) w band+
      s*generatedReadyRowCost (2*band+1) q w band+closedCouplingSourceMaskCost s t band a b+
      s*(32*band*w+22*band+146*w+141)+band*(62*w+35)+154+24*(liftedCoefficientWidth P q w s t u band)+4 := by
  simp only [spatialCouplingRowsCost,prepareSpatialCouplingSourceCost,
    prepareMaskedCouplingSourceCost,maskCouplingSourceCost,padCouplingSourceCost,
    runSpatialCouplingRowsCost,runPreparedPacketCouplingRowsCost,packetSpatialCouplingRowLoopCost,
    packetSpatialCouplingRowStepCost,packetSpatialCouplingRowCost,prepareCountedCouplingInputsCost,
    copyCountedLineCost,transferCountedLineCost,retireSpatialCouplingSourceCost,
    retireCountedLineCost,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
