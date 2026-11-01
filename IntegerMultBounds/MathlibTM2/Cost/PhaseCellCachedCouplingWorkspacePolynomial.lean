module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryNumericalWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedPreparedSharedLocalFeed

/-! Cached coupling needs polynomial shared scratch under a common physical envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem cachedLocalCouplingWorkspace_poly {P M q w s t u band a b origin N V Z : ℕ}
    (hZ : 1 ≤ Z) (hM : M ≤ Z) (hw : w ≤ Z) (hN : N ≤ Z) (hV : V ≤ Z)
    (hband : band ≤ Z) (hrows : 2*band+1 ≤ Z)
    (hpage : (couplingCoefficientPageInterval P q s t u band a b origin N).length ≤ Z)
    (hprepare : mnProgPush (cachedPreparedLocalRibbon (P := Empty) (Q := Q) (A := A) (U := U) 159) ≤ Z)
    (hrelease : mnProgPush (releaseCouplingRibbon (P := Empty) (Q := Q) (A := A) (U := U)) ≤ Z) :
    cachedLocalCouplingWorkspace (Q := Q) (A := A) (U := U) P M q w s t u band a b origin N V ≤
      200000*(ssMulConst+1)*Z^4 := by
  have hr := realWeightWorkspace_poly hZ hM hw hrows
  have hm : cachedLocalCouplingWorkspace (Q := Q) (A := A) (U := U) P M q w s t u band a b origin N V ≤
      Z*((16*Z*Z+21*Z+14*Z*Z+13*Z+11*Z+46)+cachedGatheredRibbonCost (Z+2*Z) Z+
        (12*((Z+2*Z)*Z)+11*(Z+2*Z)+14))+
      ((2*(6*Z+6)+(3*(6*Z+11*Z+6)+((1000*(ssMulConst+1)*Z^4+13000*(Z+1)*(Z+1))+
        3*(22*Z+22*Z+22+transferCountedLineCost Z Z+transferCountedLineCost Z Z))))+
        Z*(12*((Z+2*Z)*Z)+17*Z+26*Z+11*Z+24)) := by
    unfold cachedLocalCouplingWorkspace cachedGatheredRibbonCost maskCouplingSourceCost transferCountedLineCost
    gcongr
  have h3 : Z^3 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h2 : Z^2 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h1 : Z ≤ Z^4 := Nat.le_self_pow (by decide) Z
  have h0 : 1 ≤ Z^4 := Nat.one_le_pow _ _ hZ
  have hs : Z^4 ≤ (ssMulConst+1)*Z^4 := Nat.le_mul_of_pos_left _ (by omega)
  unfold cachedGatheredRibbonCost maskCouplingSourceCost transferCountedLineCost at hm
  nlinarith only [hm,h3,h2,h1,h0,hs]

theorem cachedPreparedSharedLocalFeedCouplingWorkspace_poly {P M q w s t u band a b origin N V Z : ℕ}
    (hZ : 1 ≤ Z) (hM : M ≤ Z) (hq : q ≤ Z) (hw : w ≤ Z) (hwpos : 1 ≤ w)
    (hN : N ≤ Z) (hV : V ≤ Z) (hband : band ≤ Z) (hrows : 2*band+1 ≤ Z)
    (hpage : (couplingCoefficientPageInterval P q s t u band a b origin N).length ≤ Z)
    (hprepare : mnProgPush (cachedPreparedLocalRibbon (P := Empty) (Q := Q) (A := A) (U := U) 159) ≤ Z)
    (hrelease : mnProgPush (releaseCouplingRibbon (P := Empty) (Q := Q) (A := A) (U := U)) ≤ Z)
    (hfeed : mnProgPush (feedPackedCouplingResult (P₀ := Empty) (Q := Q) (A := A) (U := U)) ≤ Z) :
    cachedPreparedSharedLocalFeedCouplingWorkspace (Q := Q) (A := A) (U := U) P M q w s t u band a b origin N V ≤
      400000*(ssMulConst+1)*Z^4 := by
  have hl := cachedLocalCouplingWorkspace_poly hZ hM hw hN hV hband hrows hpage hprepare hrelease
  have hp := scalarPrepareCost_arg_le hq hw hwpos
  have hm : cachedPreparedSharedLocalFeedCouplingWorkspace (Q := Q) (A := A) (U := U) P M q w s t u band a b origin N V ≤
      3*(20020*Z^3+6*Z+4*Z+10)+(200000*(ssMulConst+1)*Z^4+Z*(28*Z*Z+36*Z+11*Z+26)) := by
    unfold cachedPreparedSharedLocalFeedCouplingWorkspace
    gcongr
  have h3 : Z^3 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h2 : Z^2 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h1 : Z ≤ Z^4 := Nat.le_self_pow (by decide) Z
  have h0 : 1 ≤ Z^4 := Nat.one_le_pow _ _ hZ
  have hs : Z^4 ≤ (ssMulConst+1)*Z^4 := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith only [hm,h3,h2,h1,h0,hs]

end IntegerMultBounds.MathlibTM2.Cost
