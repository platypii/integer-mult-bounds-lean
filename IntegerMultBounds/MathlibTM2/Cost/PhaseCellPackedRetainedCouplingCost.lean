module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellUncachedCouplingPolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedSharedLocalFeedCouplingInterval

/-! Retained interval coupling reuses the established scalar multiplication
estimate. Its counted loop is bounded structurally for either skip outcome. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem retainedPageSpatialGuardedStepCost_poly {q w band Z : ℕ}
    (hZ : 1 ≤ Z) (hq : q ≤ Z) (hw : w ≤ Z) (hpos : 1 ≤ w) (hband : band ≤ Z) (skip : Bool) :
    retainedPageSpatialGuardedStepCost skip q w band ≤ 200000*(ssMulConst+1)*Z^4 := by
  let S := ssMulConst+1
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have hrow := generatedReadyRowCost_poly hZ hq hw hpos hband
  have hretained : retainedCouplingRowCost (2*band+1) w ≤ generatedReadyRowCost (2*band+1) q w band := by
    unfold retainedCouplingRowCost generatedReadyRowCost
    omega
  have hcopy : copyCountedLineCost (2*band+1) w+prepareCountedCouplingInputsCost band w+
      transferCountedLineCost (2*band+1) w ≤
      ((2*Z+1)*(16*Z+9)+16)+(4*Z+5+((2*Z+1)*(16*Z+9)+16))+((2*Z+1)*(10*Z+9)+10) := by
    unfold prepareCountedCouplingInputsCost copyCountedLineCost transferCountedLineCost
    gcongr
  have hpow (j : ℕ) (hj : j ≤ 4) : Z^j ≤ Z^4 := Nat.pow_le_pow_right hZ hj
  have hscale : Z^4 ≤ S*Z^4 := Nat.le_mul_of_pos_left _ hS
  cases skip with
  | true =>
    simp only [retainedPageSpatialGuardedStepCost,retainedGuardedPageSpatialCouplingRowCost,ite_true]
    change _ ≤ 200000*S*Z^4
    nlinarith only [hw,hpow 0 (by decide),hpow 1 (by decide),hscale]
  | false =>
    simp only [retainedPageSpatialGuardedStepCost,retainedGuardedPageSpatialCouplingRowCost,
      Bool.false_eq_true,ite_false,retainedConsumePageSpatialCouplingRowCost,retainedPageSpatialCouplingRowCost]
    change _ ≤ 200000*S*Z^4
    dsimp only [S] at hscale ⊢
    nlinarith only [hrow,hretained,hcopy,hw,hpow 0 (by decide),hpow 1 (by decide),hpow 2 (by decide),hscale]

theorem retainedPageSpatialIntervalLoopCost_poly {q w s t band a b origin Z : ℕ}
    (hZ : 1 ≤ Z) (hq : q ≤ Z) (hw : w ≤ Z) (hpos : 1 ≤ w) (hband : band ≤ Z)
    (boundary : Bool) (N : ℕ) :
    retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N ≤
      N*(200000*(ssMulConst+1)*Z^4+3)+2 := by
  unfold retainedPageSpatialIntervalLoopCost
  apply Nat.add_le_add_right
  calc
    _ ≤ (Finset.range N).sum (fun _ => 200000*(ssMulConst+1)*Z^4+3) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.add_le_add_right (retainedPageSpatialGuardedStepCost_poly hZ hq hw hpos hband _) 3
    _ = _ := by simp

/-- Preparation, retained row arithmetic and tape cleanup share a polynomial
allowance over the actual interval length. Coefficients are read from the retained page. -/
theorem preparedSharedLocalFeedCouplingIntervalCost_poly {P q w s t u band a b origin N V Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hN : N ≤ t)
    (hq : q ≤ Z) (hw : w ≤ Z) (hpos : 1 ≤ w) (hband : band ≤ Z) (hV : V ≤ Z)
    (boundary : Bool) :
    preparedSharedLocalFeedCouplingIntervalCost boundary P q w s t u band a b origin N V ≤
      1000000*(ssMulConst+1)*t*Z^4 := by
  let S := ssMulConst+1
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have hprepare := scalarPrepareCost_arg_le hq hw hpos
  have htop := (Schoenhage.Schedule.topN_facts hpos).2.1.trans (Nat.mul_le_mul_left 4 hw)
  have hloop := retainedPageSpatialIntervalLoopCost_poly (s := s) (t := t) (a := a) (b := b)
    (origin := origin) hZ hq hw hpos hband boundary N
  have hloop' := hloop.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hN) 2)
  have hlen := couplingCoefficientPageInterval_length_le P q s t u band a b origin N
  have hprod := Nat.mul_le_mul hN (show 2*band+1 ≤ 3*Z by omega)
  have hwords : (couplingCoefficientPageInterval P q s t u band a b origin N).length ≤ 3*t*Z := by
    nlinarith only [hlen,hprod]
  have hmono : preparedSharedLocalFeedCouplingIntervalCost boundary P q w s t u band a b origin N V ≤
    ((20020*Z^3)+6*Z+4*Z+10)+((((16*t*Z+21*t+14*Z*Z+13*Z+11*Z+46)+(152*Z+153+((32*(t+2*Z)+2)*tblC Z 1+68*Z+2*(t+2*Z)+72)+maskCouplingSourceCost (t+2*Z) Z)+(12*((t+2*Z)*Z)+11*(t+2*Z)+14)) +
        (12*((t+2*Z)*Z)+17*t+26*Z+11*Z+24) +
        (144*Z+145+((46*t+2)*tblC Z 1+66*Z+2*t+70)+(6*t+11*Z+6+((t*(200000*(ssMulConst+1)*Z^4+3)+2)+
        (22*t+22*Z+22+transferCountedLineCost t Z+
          transferCountedLineCost (3*t*Z) Z))))) + (28*t*Z+36*t+11*Z+26))+2*(Z+Z+(4*Z))+7 := by
    unfold preparedSharedLocalFeedCouplingIntervalCost maskCouplingSourceCost transferCountedLineCost tblC
    gcongr
  have hp (j : ℕ) (hj : j ≤ 4) : Z^j ≤ Z^4 := Nat.pow_le_pow_right hZ hj
  have htScale (j : ℕ) (hj : j ≤ 4) : t*Z^j ≤ t*Z^4 := Nat.mul_le_mul_left t (hp j hj)
  have hZt : Z^4 ≤ t*Z^4 := Nat.le_mul_of_pos_left _ ht
  have hshared : t*Z^4 ≤ S*t*Z^4 := by
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left (t*Z^4) hS
  dsimp only [S] at hshared
  unfold maskCouplingSourceCost transferCountedLineCost at hmono
  simp only [tblC] at hmono
  nlinarith only [hmono,hp 0 (by decide),hp 1 (by decide),hp 2 (by decide),hp 3 (by decide),
    htScale 0 (by decide),htScale 1 (by decide),htScale 2 (by decide),htScale 3 (by decide),hZt,hshared]

end IntegerMultBounds.MathlibTM2.Cost
