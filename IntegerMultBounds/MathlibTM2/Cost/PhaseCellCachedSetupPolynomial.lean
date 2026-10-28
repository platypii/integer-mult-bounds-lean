module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellNumericalSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchCost
public import IntegerMultBounds.MathlibTM2.Cost.MatchConv

/-! The zero-cell cached batch pays numerical construction plus polynomial formatting. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.Schoenhage IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem scalarPrepareCost_arg_le {a w Z : ℕ} (ha : a ≤ Z) (hw : w ≤ Z) (hpos : 1 ≤ w) :
    prepareCost a w ≤ 20020*Z^3 := by
  have heq : prepareCost a w = prepareCost 0 w+a*(4*w+16) := by
    simp only [prepareCost,counterSetupCost,chirpMultiplierSetupCost]
    ring
  have hp := (scalarPrepareCost_le w hpos).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 3))
  have hZ := hpos.trans hw
  have hprod := Nat.mul_le_mul ha (show 4*w+16 ≤ 4*Z+16 by omega)
  have hsq : Z ≤ Z^2 := by nlinarith only [hZ]
  have hcub : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left (Z^2) hZ]
  rw [heq]
  nlinarith only [hp,hprod,hsq,hcub]

theorem fixedEmptyBatchCost_le {q l w Z : ℕ} (hq : 1 ≤ q) (hl : l ≤ q)
    (hwq : w ≤ 10*q) (hqZ : q ≤ Z) (hwZ : w ≤ Z) (hrZ : 2^l ≤ Z) :
    Fixed.cost q l w 0 ≤ (2*mtCvKf 10+300)*Z^2 := by
  have hfix := mt_cv_fix_le hq hl hwq (Nat.le_add_right (2^l) q) (Nat.le_add_left q (2^l))
  have hX : 2^l+q ≤ 2*Z := by omega
  have hprod := Nat.mul_le_mul hX hqZ
  have hfix' : rpFixCost q l w ≤ 2*mtCvKf 10*Z^2 := by
    have hm := Nat.mul_le_mul_left (mtCvKf 10) hprod
    nlinarith only [hfix,hm]
  have hheader := ring_header_length_le q (2^l) w
  have hheader' : (Spec.SignedRingProduct.header q (2^l) w).length ≤ 6*Z := by omega
  have hlZ := hl.trans hqZ
  have hZ := hq.trans hqZ
  have hsq : Z ≤ Z^2 := by nlinarith only [hZ]
  have hvol := Nat.mul_le_mul hrZ hwZ
  unfold Fixed.cost ldrHeaderCost
  simp only [Nat.zero_mul,Nat.zero_add]
  nlinarith only [hfix',hheader',hlZ,hqZ,hwZ,hvol,hsq,hZ]

theorem cachedClosedBatchCost_zero_poly {p l L s t u target rhsExp Z : ℕ}
    (hZ : 1 ≤ Z) (hp : p ≤ Z) (hl : l ≤ Z) (hL : L ≤ Z)
    (hr : 2^l ≤ Z) (hw : executionWidth p l target rhsExp ≤ Z)
    (hW : integerSetupWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionStagePrecision p l target rhsExp+2) 0 ≤ Z) :
    cachedClosedBatchCost p l 0 L s t u target rhsExp ≤
      headerGeneratorSetupCost (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) s t u (PhaseCellBand.width p u) L+
        (8*mtCvKf 10+1000000)*Z^3 := by
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let N := executionStagePrecision p l target rhsExp+1
  let W := integerSetupWidth (2^15*p) q (N+1) 0
  let E := executionExponent p l target rhsExp
  have hqpos : 1 ≤ q := by dsimp [q,executionPrecision,executionExponent,inputExponent,sourceExponent]; omega
  have hwpos : 1 ≤ w := by dsimp [w,executionWidth]; omega
  have hWpos : 1 ≤ W := by dsimp [W,integerSetupWidth]; omega
  have hq : q ≤ Z := by
    have hh : q ≤ w := by dsimp [q,w,executionPrecision,executionWidth]; omega
    exact hh.trans hw
  have hN : N ≤ Z := by
    have hh : N ≤ w := by dsimp [N,w,executionStagePrecision,executionWidth]; omega
    exact hh.trans hw
  have hP : 2^15*p ≤ Z := by
    have hh : 2^15*p ≤ W := by dsimp [W,integerSetupWidth]; nlinarith only [Nat.zero_le (N*(2^15*p))]
    exact hh.trans hW
  have hE : E ≤ Z := by
    have hh : E ≤ w := by dsimp [E,w,executionWidth]; omega
    exact hh.trans hw
  have hqwE : q+E ≤ Z := by
    have hh : q+E ≤ w := by dsimp [q,E,w,executionPrecision,executionWidth]; omega
    exact hh.trans hw
  have hfixed := fixedEmptyBatchCost_le hqpos
    (show l ≤ q by dsimp [q,executionPrecision,executionExponent,inputExponent,sourceExponent]; omega)
    (show w ≤ 10*q by dsimp [w,q,executionWidth,executionPrecision,executionExponent,inputExponent,sourceExponent]; omega) hq hw hr
  have hprepare := scalarPrepareCost_arg_le hq hw hwpos
  have hprepareE := scalarPrepareCost_arg_le hqwE hw hwpos
  have htop := (Schoenhage.Schedule.topN_facts hwpos).2.1
  have htopW := (Schoenhage.Schedule.topN_facts hWpos).2.1
  have hL2 := Nat.mul_le_mul hL hL
  have hL2W := Nat.mul_le_mul hL2 hW
  have hLW := Nat.mul_le_mul hL hw
  have hrw := Nat.mul_le_mul hr hw
  have hsq : Z ≤ Z^2 := by nlinarith only [hZ]
  have hcub : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left (Z^2) hZ]
  have hscaled := Nat.mul_le_mul_left (mtCvKf 10) hcub
  have hqw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  simp only [cachedClosedBatchCost,cachedGeneratedBatchSetupCost,cachedBatchWeightedSetupCost,
    preparedBatchWeightedSetupCost,batchInverseSetupCost,prepareBatchGeneratorPageCost,
    replicateGeneratorsCost,prepareBatchRuntimeCost,swapBatchPayloadCost,installBatchHeadersCost,
    stagePayloadCost,fetchPageCost,cellArithmeticCost,inputStageCost,closedWeightsCost,
    prepareWeightsCost,installInputCost,interiorProductsCost,compactPairCost,pairFinishCost,
    fixedMergeCost,fetchScalarCost,preparedOutputCost,fetchOutputTableCost,outputFromHeadersCost,
    closedOutputWeightsCost,publishFromDimensionsCost,releaseBatchRuntimeCost,releaseRuntimePagesCost,
    runWeightsCost,runCost,routeWeightsCost,routeCost,scaleOutputPrefixCost,swapCellPayloadCost,
    releaseGeneratorPageCost,releaseWeightPageCost,releaseConstructionCost,releaseFactorPageCost,
    releaseWeightCountersCost,Nat.zero_mul,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
  simp only [show 2*executionPrecision p l target rhsExp+8 = executionWidth p l target rhsExp from hqw]
  dsimp only [q,w,N,W,E] at hq hN hE hfixed hprepare hprepareE htop htopW hL2W hLW hrw
  simp only [executionExponent,inputExponent] at hprepareE hE ⊢
  nlinarith only [hscaled,hP,hq,hN,hE,hfixed,hprepare,hprepareE,htop,htopW,hL2W,hLW,hrw,
    hl,hL,hW,hw,hp,hZ,hsq,hcub]

end IntegerMultBounds.MathlibTM2.Cost
