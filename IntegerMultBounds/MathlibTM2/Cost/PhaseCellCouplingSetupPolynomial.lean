module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingKeyControls

/-! Price the actual coupling coefficient generator and its counted row loop.
Only the already priced geometry mask remains separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem couplingCoefficientPageRowCost_poly {P q w s t u band Z : ℕ}
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hw : w ≤ Z) (hband : band ≤ Z)
    (hV : liftedCoefficientWidth P q w s t u band ≤ Z) (skip : Bool) :
    couplingCoefficientPageRowCost skip P q w s t u band ≤ 2000000*Z^4 := by
  let V := liftedCoefficientWidth P q w s t u band
  have hp2 : Z ≤ Z^2 := by nlinarith only [hZ]
  have hp3 : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left (Z^2) hZ]
  have hp4 : Z^3 ≤ Z^4 := by nlinarith only [Nat.mul_le_mul_left (Z^3) hZ]
  have htable : tblC V w ≤ 808*Z^2 := by
    have hs := Nat.pow_le_pow_left (show V+4 ≤ 5*Z by dsimp only [V]; omega) 2
    unfold tblC
    nlinarith only [hs,hw,hp2]
  cases skip with
  | true =>
    simp only [couplingCoefficientPageRowCost,ite_true]
    nlinarith only [hV,hZ,hp2,hp3,hp4]
  | false =>
    have hm : couplingCoefficientPageRowCost false P q w s t u band ≤
        (((310*Z+2*Z*(620*Z+256)+131)*(808*Z^2)+658*Z+4*Z+2*((2*Z+1)*Z)+647)+22*Z+25)+
        ((2*Z+1)*(10*Z+9)+10)+4*(2*Z+1)+4+1 := by
      unfold couplingCoefficientPageRowCost prepareCouplingCoefficientRowCost markedRowCoefficientCost
        rowCoefficientFromPacketCost transferCountedLineCost
      simp only [Bool.false_eq_true,ite_false]
      gcongr
    nlinarith only [hm,hZ,hp2,hp3,hp4]

theorem couplingCoefficientPageIntervalLoopCost_poly {P q w s t u band a b origin Z : ℕ}
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hw : w ≤ Z) (hband : band ≤ Z)
    (hV : liftedCoefficientWidth P q w s t u band ≤ Z) (N : ℕ) :
    couplingCoefficientPageIntervalLoopCost P q w s t u band a b origin N ≤ N*(2000000*Z^4+4)+2 := by
  have hs : (Finset.range N).sum (fun i =>
      couplingCoefficientPageRowCost (couplingSkipAt true s t band a b (origin+i)) P q w s t u band+4) ≤
      N*(2000000*Z^4+4) := by
    calc
      _ ≤ (Finset.range N).sum (fun _ => 2000000*Z^4+4) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.add_le_add_right (couplingCoefficientPageRowCost_poly hZ hP hw hband hV _) 4
      _ = _ := by simp
  exact Nat.add_le_add_right hs 2

theorem couplingCoefficientPageLoopCost_poly {P q w s t u band a b Z : ℕ}
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hw : w ≤ Z) (hband : band ≤ Z)
    (hV : liftedCoefficientWidth P q w s t u band ≤ Z) (N : ℕ) :
    couplingCoefficientPageLoopCost P q w s t u band a b N ≤ N*(2000000*Z^4+4)+2 := by
  simpa [couplingCoefficientPageLoopCost,couplingCoefficientPageIntervalLoopCost] using
    couplingCoefficientPageIntervalLoopCost_poly (origin := 0) hZ hP hw hband hV N

theorem buildMarkedRowCoefficientPacketCost_zero_poly {P q w s t u band Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hs : s ≤ t)
    (hP : P ≤ Z) (hq : q ≤ Z) (hw : w ≤ Z) (hu : u ≤ Z) (hband : band ≤ Z)
    (hV : liftedCoefficientWidth P q w s t u band ≤ Z) :
    buildMarkedRowCoefficientPacketCost P q w s t u band 0 ≤ 1000000*t*Z^3 := by
  let V := liftedCoefficientWidth P q w s t u band
  have hp2 : Z ≤ Z^2 := by nlinarith only [hZ]
  have hp3 : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left (Z^2) hZ]
  have htable : tblC V w ≤ 808*Z^2 := by
    have hs := Nat.pow_le_pow_left (show V+4 ≤ 5*Z by dsimp only [V]; omega) 2
    unfold tblC
    nlinarith only [hs,hw,hp2]
  have hm : buildMarkedRowCoefficientPacketCost P q w s t u band 0 ≤
      (4*Z+4*Z+4*Z+152*(t+t+Z+Z)+270)+
      (((304*Z+4*Z+409)+((Z+Z+t+t+Z+0+Z)*(4*Z+10)+42*Z+71))+
        (154*Z+4*Z+413)*(808*Z^2)+240*Z+244)+6*Z+7 := by
    unfold buildMarkedRowCoefficientPacketCost generateLiftedCoefficientWidthCost buildPreparedRowPacketCost
      initializeRowCoefficientHeadersCost
    dsimp only
    gcongr
  have htZ := Nat.mul_le_mul_left t hp2
  have htZ2 := Nat.mul_le_mul_left t hp3
  have hZt := Nat.mul_le_mul_left (Z^3) ht
  have htz := Nat.mul_le_mul_left t hZ
  nlinarith only [hm,ht,hZ,hp2,hp3,htZ,htZ2,hZt,htz]

/-- Starting at a halo origin pays only its actual binary-header construction. -/
theorem buildMarkedRowCoefficientPacketCost_origin (P q w s t u band origin : ℕ) :
    buildMarkedRowCoefficientPacketCost P q w s t u band origin =
      buildMarkedRowCoefficientPacketCost P q w s t u band 0+
        origin*(4*liftedCoefficientWidth P q w s t u band+10) := by
  unfold buildMarkedRowCoefficientPacketCost buildPreparedRowPacketCost initializeRowCoefficientHeadersCost
  ring

theorem buildMarkedRowCoefficientPacketCost_origin_poly {P q w s t u band origin Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hs : s ≤ t) (hi : origin ≤ s)
    (hP : P ≤ Z) (hq : q ≤ Z) (hw : w ≤ Z) (hu : u ≤ Z) (hband : band ≤ Z)
    (hV : liftedCoefficientWidth P q w s t u band ≤ Z) :
    buildMarkedRowCoefficientPacketCost P q w s t u band origin ≤ 2000000*t*Z^3 := by
  have hz := buildMarkedRowCoefficientPacketCost_zero_poly ht hZ hs hP hq hw hu hband hV
  have hlin : origin*(4*liftedCoefficientWidth P q w s t u band+10) ≤ t*(14*Z) :=
    Nat.mul_le_mul (hi.trans hs) (by omega)
  have hp2 : Z ≤ Z^2 := by nlinarith only [hZ]
  have hp3 : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left (Z^2) hZ]
  have hm := Nat.mul_le_mul_left t (show 14*Z ≤ 1000000*Z^3 by omega)
  rw [buildMarkedRowCoefficientPacketCost_origin]
  nlinarith only [hz,hlin,hm]

theorem buildCouplingPageCacheCost_poly {P q w s t u band a b Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hs : s ≤ t)
    (hP : P ≤ Z) (hq : q ≤ Z) (hw : w ≤ Z) (hu : u ≤ Z) (hband : band ≤ Z)
    (hV : liftedCoefficientWidth P q w s t u band ≤ Z) :
    buildCouplingPageCacheCost P q w s t u band a b ≤
      2*prepareCouplingGuardCost s t band a b+4000000*t*Z^4 := by
  have hpacket := buildMarkedRowCoefficientPacketCost_zero_poly ht hZ hs hP hq hw hu hband hV
  have hloop := couplingCoefficientPageLoopCost_poly (a := a) (b := b) hZ hP hw hband hV s
  have hlen := couplingCoefficientPage_length_le P q s t u band a b s
  have hprod := Nat.mul_le_mul hs (show 2*band+1 ≤ 3*Z by omega)
  have hwords : (couplingCoefficientPage P q s t u band a b s).length ≤ 3*t*Z := by
    nlinarith only [hlen,hprod]
  have htransfer : transferCountedLineCost (couplingCoefficientPage P q s t u band a b s).length w ≤
      (3*t*Z)*(10*Z+9)+10 := by unfold transferCountedLineCost; gcongr
  have hloop' := hloop.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hs) 2)
  have hp2 : Z ≤ Z^2 := by nlinarith only [hZ]
  have hp3 : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left (Z^2) hZ]
  have hp4 : Z^3 ≤ Z^4 := by nlinarith only [Nat.mul_le_mul_left (Z^3) hZ]
  have htZ := Nat.mul_le_mul_left t hp2
  have htZ2 := Nat.mul_le_mul_left t hp3
  have htZ3 := Nat.mul_le_mul_left t hp4
  have hZt := Nat.mul_le_mul_left (Z^4) ht
  have htz := Nat.mul_le_mul_left t hZ
  dsimp only [buildCouplingPageCacheCost,buildCouplingCoefficientPageCost,prepareCouplingPageCountsCost]
  nlinarith only [hpacket,hloop',htransfer,hs,hband,hV,ht,hZ,hp2,hp3,hp4,htZ,htZ2,htZ3,hZt,htz]

end IntegerMultBounds.MathlibTM2.Cost
