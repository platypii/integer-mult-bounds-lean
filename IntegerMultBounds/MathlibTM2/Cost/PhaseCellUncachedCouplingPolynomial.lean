module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCouplingSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBorrowedCouplingPass

/-! The actual uncached coupling supplier used by computed Schur columns has a
polynomial construction price, including its generated row arithmetic. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem generatedReadyRowCost_poly {q w band R : ℕ}
    (hR : 1 ≤ R) (hq : q ≤ R) (hw : w ≤ R) (hpos : 1 ≤ w) (hband : band ≤ R) :
    generatedReadyRowCost (2*band+1) q w band ≤ 100000*(ssMulConst+1)*R^4 := by
  let S := ssMulConst+1
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have hprepare := scalarPrepareCost_arg_le hq hw hpos
  have hMul := band_rmul_le hw hR
  have htop := (Schoenhage.Schedule.topN_facts hpos).2.1
  have htop' : Schoenhage.Schedule.topN w ≤ 4*R := htop.trans (Nat.mul_le_mul_left 4 hw)
  have hm : generatedReadyRowCost (2*band+1) q w band ≤
      20020*R^3+(2*R+1)*(288*S*R^3+61*R+32)+32*R+8*R+4*R+2*(4*R)+109 := by
    unfold generatedReadyRowCost
    gcongr
  have hp (j : ℕ) (hj : j ≤ 4) : R^j ≤ R^4 := Nat.pow_le_pow_right hR hj
  have hs (j : ℕ) (hj : j ≤ 4) : S*R^j ≤ S*R^4 := Nat.mul_le_mul_left S (hp j hj)
  have hRS : R^4 ≤ S*R^4 := by simpa using Nat.mul_le_mul_right (R^4) hS
  change _ ≤ 100000*S*R^4
  nlinarith only [hm,hp 0 (by decide),hp 1 (by decide),hp 2 (by decide),hp 3 (by decide),
    hs 0 (by decide),hs 1 (by decide),hs 2 (by decide),hs 3 (by decide),hRS]

theorem packetSpatialGuardedStepCost_poly {P q w s t u band R : ℕ}
    (hR : 1 ≤ R) (hP : P ≤ R) (hq : q ≤ R) (hw : w ≤ R) (hpos : 1 ≤ w) (hband : band ≤ R)
    (hV : liftedCoefficientWidth P q w s t u band ≤ R) (skip : Bool) :
    packetSpatialGuardedStepCost skip P q w s t u band ≤ 4000000*(ssMulConst+1)*R^4 := by
  let S := ssMulConst+1
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have hcoeff := couplingCoefficientPageRowCost_poly hR hP hw hband hV false
  have hmarked : markedRowCoefficientCost P q (liftedCoefficientWidth P q w s t u band) w band ≤ 2000000*R^4 := by
    dsimp only [couplingCoefficientPageRowCost,prepareCouplingCoefficientRowCost] at hcoeff
    simp only [Bool.false_eq_true,ite_false] at hcoeff
    omega
  have hrow := generatedReadyRowCost_poly hR hq hw hpos hband
  have hinputs : prepareCountedCouplingInputsCost band w ≤ 4*R+5+((2*R+1)*(16*R+9)+16) := by
    unfold prepareCountedCouplingInputsCost copyCountedLineCost
    gcongr
  have hp1 : R ≤ R^4 := by simpa using Nat.pow_le_pow_right hR (show 1 ≤ 4 by decide)
  have hp2 : R^2 ≤ R^4 := Nat.pow_le_pow_right hR (by decide)
  have hRS : R^4 ≤ S*R^4 := by simpa using Nat.mul_le_mul_right (R^4) hS
  cases skip with
  | true =>
    simp only [packetSpatialGuardedStepCost,ite_true,zeroPacketSpatialCouplingRowCost]
    change _ ≤ 4000000*S*R^4
    nlinarith only [hV,hw,hR,hp1,hRS]
  | false =>
    simp only [packetSpatialGuardedStepCost,Bool.false_eq_true,ite_false,packetSpatialCouplingRowCost]
    dsimp only [S] at hRS
    nlinarith only [hmarked,hrow,hinputs,hw,hR,hp1,hp2,hRS]

theorem packetSpatialGuardedLoopCost_poly {P q w s t u band a b R : ℕ}
    (hR : 1 ≤ R) (hP : P ≤ R) (hq : q ≤ R) (hw : w ≤ R) (hpos : 1 ≤ w) (hband : band ≤ R)
    (hV : liftedCoefficientWidth P q w s t u band ≤ R) (boundary : Bool) (N : ℕ) :
    packetSpatialGuardedLoopCost boundary P q w s t u band a b N ≤
      N*(4000000*(ssMulConst+1)*R^4+3)+2 := by
  have hs : (Finset.range N).sum (fun j => packetSpatialGuardedStepCost
      (couplingSkipAt boundary s t band a b j) P q w s t u band+3) ≤
      N*(4000000*(ssMulConst+1)*R^4+3) := by
    calc
      _ ≤ (Finset.range N).sum (fun _ => 4000000*(ssMulConst+1)*R^4+3) := by
        apply Finset.sum_le_sum
        intro j hj
        exact Nat.add_le_add_right (packetSpatialGuardedStepCost_poly hR hP hq hw hpos hband hV _) 3
      _ = _ := by simp
  exact Nat.add_le_add_right hs 2

theorem borrowedCouplingPassCost_poly {P q w s t u band a b R : ℕ}
    (hR : 1 ≤ R) (ht : 1 ≤ t) (hst : s ≤ t) (htR : t ≤ R)
    (hP : P ≤ R) (hq : q ≤ R) (hw : w ≤ R) (hpos : 1 ≤ w) (hu : u ≤ R) (hband : band ≤ R)
    (hV : liftedCoefficientWidth P q w s t u band ≤ R) (boundary : Bool) :
    borrowedCouplingPassCost boundary P q w s t u band a b ≤
      closedCouplingSourceMaskCost s t band a b+prepareCouplingGuardCost s t band a b+
        10000000*(ssMulConst+1)*R^5 := by
  let S := ssMulConst+1
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have hs : s ≤ R := hst.trans htR
  have hpacket := buildMarkedRowCoefficientPacketCost_zero_poly ht hR hst hP hq hw hu hband hV
  have hloop := packetSpatialGuardedLoopCost_poly (a := a) (b := b) hR hP hq hw hpos hband hV boundary s
  have hclock := Nat.mul_le_mul_right (4000000*S*R^4+3) hs
  have hpacketScale := Nat.mul_le_mul_right (1000000*R^3) htR
  have hmul := Nat.mul_le_mul hs hw
  have hbandMul := Nat.mul_le_mul hband hw
  have hp (j : ℕ) (hj : j ≤ 5) : R^j ≤ R^5 := Nat.pow_le_pow_right hR hj
  have hRS : R^5 ≤ S*R^5 := by simpa using Nat.mul_le_mul_right (R^5) hS
  dsimp only [borrowedCouplingPassCost,runCouplingRowsCost,spatialCouplingGuardedRowsCost,
    prepareSpatialCouplingSourceCost,prepareMaskedCouplingSourceCost,maskCouplingSourceCost,
    padCouplingSourceCost,runSpatialCouplingGuardedCost,runPreparedPacketGuardedCost,
    transferCountedLineCost,retireSpatialCouplingSourceCost,retireCountedLineCost]
  dsimp only [S] at hclock hRS
  nlinarith only [hpacket,hloop,hclock,hpacketScale,hmul,hbandMul,hs,hband,hw,hV,hR,
    hp 0 (by decide),hp 1 (by decide),hp 2 (by decide),hp 3 (by decide),hp 4 (by decide),hRS]

end IntegerMultBounds.MathlibTM2.Cost
