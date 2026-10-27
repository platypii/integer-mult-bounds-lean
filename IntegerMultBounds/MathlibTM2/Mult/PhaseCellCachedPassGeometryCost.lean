module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCachedRestoredCouplingPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPageCouplingCost

/-! Carry the active-row page-reader bound through source staging and header restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- A complete cached pass pays row arithmetic only on the geometric boundary neighbourhood. -/
def placedCachedCouplingGeometryCost (P q s t u band a b : ℕ) : ℕ :=
  let w := 2*q+8
  installCouplingHeadersCost P q s t u band a b+
    (prepareSpatialCouplingSourceCost s t band a b w+
      (10*s+10+runPreparedPageCouplingRowsGeometryCost q w s t band a b)+
      retireSpatialCouplingSourceCost s band w+50*s*w+27*s+50+
      releaseCouplingHeadersCost P q s t u band a b)

theorem placedCachedRestoredCouplingPassCost_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (boundary : Bool) (P q u band a b : ℕ) (hb : b ≤ s) :
    placedCachedRestoredCouplingPassCost boundary P q s t u band a b
        (couplingCoefficientPage P q s t u band a b s).length ≤
      placedCachedCouplingGeometryCost P q s t u band a b := by
  have h := runCachedPageCouplingRowsCost_geometry_le hst boundary P q (2*q+8) u band a b hb
  dsimp only [placedCachedRestoredCouplingPassCost,placedCachedFeedCouplingPassCost,
    placedCachedBorrowedCouplingPassCost,placedCachedSpatialCouplingRowsCost,
    placedCachedCouplingGeometryCost]
  nlinarith only [h]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
