module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingRows

/-! Separate actual coefficient generation, row arithmetic, mask setup and stream work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem spatialCouplingRowsCost_eq (P q w s t u band a b : ℕ) :
    spatialCouplingRowsCost P q w s t u band a b =
      (Finset.range s).sum (fun i => generateCouplingCoefficientsCost P q w s t u band i)+
      s*generatedReadyRowCost (2*band+1) q w band+closedCouplingSourceMaskCost s t band a b+
      s*(64*band*w+50*band+146*w+161)+band*(62*w+35)+154 := by
  simp only [spatialCouplingRowsCost,prepareSpatialCouplingSourceCost,
    prepareMaskedCouplingSourceCost,maskCouplingSourceCost,padCouplingSourceCost,
    runSpatialCouplingRowsCost,spatialCouplingRowLoopCost,spatialCouplingRowStepCost,
    spatialCouplingRowCost_eq,transferCountedLineCost,retireSpatialCouplingSourceCost,
    retireCountedLineCost,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
