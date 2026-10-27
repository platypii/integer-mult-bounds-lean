module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredCouplingPass

/-! Mode-specific executed coupling costs, with source transport and actual recovery branch counts. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem feedCouplingPassCost_eq (boundary : Bool) (P q w s t u band a b : ℕ) :
    feedCouplingPassCost boundary P q w s t u band a b =
      spatialCouplingGuardedRowsCost boundary P q w s t u band a b+50*s*w+27*s+50 := by
  dsimp [feedCouplingPassCost,borrowedCouplingPassCost,runCouplingRowsCost]
  ring

theorem restoredCouplingPassCost_eq (boundary : Bool) (P q s t u band a b : ℕ) :
    restoredCouplingPassCost boundary P q s t u band a b =
      spatialCouplingGuardedRowsCost boundary P q (2*q+8) s t u band a b+
      installCouplingHeadersCost P q s t u band a b+releaseCouplingHeadersCost P q s t u band a b+
      50*s*(2*q+8)+27*s+50 := by
  dsimp only [restoredCouplingPassCost]
  rw [feedCouplingPassCost_eq]
  ring

theorem spatialCouplingGuardedRowsCost_eq (boundary : Bool) (P q w s t u band a b : ℕ) :
    spatialCouplingGuardedRowsCost boundary P q w s t u band a b =
      prepareCouplingGuardCost s t band a b+buildMarkedRowCoefficientPacketCost P q w s t u band 0+
      (Finset.range s).sum (fun i => if couplingSkipAt boundary s t band a b i then
        zeroPacketSpatialCouplingRowCost P q w s t u band else packetSpatialCouplingRowCost P q w s t u band)+
      closedCouplingSourceMaskCost s t band a b+s*(130*w+111)+band*(62*w+35)+154+
      24*liftedCoefficientWidth P q w s t u band+4 := by
  simp only [spatialCouplingGuardedRowsCost,prepareSpatialCouplingSourceCost,
    prepareMaskedCouplingSourceCost,maskCouplingSourceCost,padCouplingSourceCost,
    runSpatialCouplingGuardedCost,runPreparedPacketGuardedCost,packetSpatialGuardedLoopCost,
    packetSpatialGuardedStepCost,transferCountedLineCost,retireSpatialCouplingSourceCost,
    retireCountedLineCost,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul]
  ring

def spatialCouplingCostBound (boundary : Bool) (P q w s t u band a b : ℕ) : ℕ :=
  prepareSpatialCouplingSourceCost s t band a b w+
    prepareCouplingGuardCost s t band a b+buildMarkedRowCoefficientPacketCost P q w s t u band 0+
    s*zeroPacketSpatialCouplingRowCost P q w s t u band+
    (haloBoundaryCountBound s t (2*band) a b+4*band)*
      packetSpatialCouplingRowCost P q w s t u band+
    s*(10*w+16)+2+32*s*w+34*s+28+transferCountedLineCost s w+
    24*liftedCoefficientWidth P q w s t u band+4+retireSpatialCouplingSourceCost s band w

theorem spatialCouplingGuardedRowsCost_le {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (P q w u band a b : ℕ) (hb : b ≤ s) :
    spatialCouplingGuardedRowsCost boundary P q w s t u band a b ≤
      spatialCouplingCostBound boundary P q w s t u band a b := by
  have h := packetSpatialGuardedLoopCost_le hst boundary P q w u band a b hb
  dsimp only [spatialCouplingGuardedRowsCost,runSpatialCouplingGuardedCost,
    runPreparedPacketGuardedCost,spatialCouplingCostBound]
  omega

theorem restoredCouplingPassCost_recovery_le {s t : ℕ} [NeZero s] (hst : s < t)
    (P q u band a b : ℕ) (hb : b ≤ s) :
    restoredCouplingPassCost true P q s t u band a b ≤
      spatialCouplingCostBound true P q (2*q+8) s t u band a b+
      installCouplingHeadersCost P q s t u band a b+releaseCouplingHeadersCost P q s t u band a b+
      50*s*(2*q+8)+27*s+50 := by
  rw [restoredCouplingPassCost_eq]
  have h := spatialCouplingGuardedRowsCost_le hst true P q (2*q+8) u band a b hb
  omega

theorem feedCouplingPassCost_residual_le {s t : ℕ} [NeZero s] (hst : s < t)
    (P q w u band a b : ℕ) (hb : b ≤ s) :
    feedCouplingPassCost false P q w s t u band a b ≤
      spatialCouplingCostBound false P q w s t u band a b+50*s*w+27*s+50 := by
  rw [feedCouplingPassCost_eq]
  have h := spatialCouplingGuardedRowsCost_le hst false P q w u band a b hb
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
