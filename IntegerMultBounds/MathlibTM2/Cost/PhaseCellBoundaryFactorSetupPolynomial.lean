module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBandPreparationPolynomial

/-! Price the actual multiplier, numerical dimension headers, Newton control
and reciprocal seed setup for the retained boundary factor bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem boundaryFactorDimensionsCost_poly {band N w R : ℕ}
    (hR : 1 ≤ R) (hband : band ≤ R) (hN : N ≤ R) (hw : w ≤ R) :
    boundaryFactorDimensionsCost band N w ≤ 100000*R^3 := by
  have hm : boundaryFactorDimensionsCost band N w ≤ boundaryFactorDimensionsCost R R R := by
    unfold boundaryFactorDimensionsCost
    dsimp only
    gcongr
  have hp2 : R ≤ R^2 := by nlinarith only [hR]
  have hp3 : R^2 ≤ R^3 := by nlinarith only [Nat.mul_le_mul_left (R^2) hR]
  have hbound : boundaryFactorDimensionsCost R R R ≤ 100000*R^3 := by
    dsimp only [boundaryFactorDimensionsCost]
    nlinarith only [hR,hp2,hp3]
  exact hm.trans hbound

theorem boundaryFactorSetupCost_poly {p q band N R : ℕ}
    (hR : 1 ≤ R) (hp : p ≤ R) (hq : q ≤ R) (hband : band ≤ R) (hN : N ≤ R)
    (hw : 2*q+8 ≤ R) : boundaryFactorSetupCost p q band N ≤ 1000000*R^3 := by
  have hscalar := scalarPrepareCost_arg_le hq hw (by omega : 1 ≤ 2*q+8)
  have hdims := boundaryFactorDimensionsCost_poly hR hband hN hw
  have hproduct := Nat.mul_le_mul hp (show q+1 ≤ R+1 by omega)
  have hsub : q-2 ≤ R := (Nat.sub_le _ _).trans hq
  have hp2 : R ≤ R^2 := by nlinarith only [hR]
  have hp3 : R^2 ≤ R^3 := by nlinarith only [Nat.mul_le_mul_left (R^2) hR]
  dsimp only [boundaryFactorSetupCost,boundaryFactorHeaderSetupCost,boundaryFactorMultiplierSetupCost,
    boundaryFactorConstantsCost,boundaryFactorNewtonHeaderCost,boundaryFactorNewtonPreludeCost,boundaryFactorSeedCost]
  nlinarith only [hscalar,hdims,hproduct,hsub,hR,hp,hq,hw,hp2,hp3]

theorem boundaryFactorPreparationCost_poly (p q band N : ℕ) :
    boundaryFactorSetupCost p q band N+
        bandAxisPrepCost (2*q+8) (12*band) (factorNewtonSteps p q) N ≤
      (1000000+10000000*(ssMulConst+1))*(p+2*q+12*band+N+100)^6 := by
  let R := p+2*q+12*band+N+100
  have hR : 1 ≤ R := by dsimp only [R]; omega
  have hp : p ≤ R := by dsimp only [R]; omega
  have hq : q ≤ R := by dsimp only [R]; omega
  have hb : band ≤ R := by dsimp only [R]; omega
  have hN : N ≤ R := by dsimp only [R]; omega
  have hw : 2*q+8 ≤ R := by dsimp only [R]; omega
  have hk : 12*band ≤ R := by dsimp only [R]; omega
  have hsteps : factorNewtonSteps p q ≤ R := by
    have hc := factorNewtonSteps_bound p q
    have hp' : Nat.size p ≤ p := Nat.size_le.mpr Nat.lt_two_pow_self
    have hq' : Nat.size (q+1) ≤ q+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    dsimp only [R]
    omega
  have hheader := boundaryFactorSetupCost_poly hR hp hq hb hN hw
  have hS : 1 ≤ ssMulConst+1 := by omega
  have hMul : rmulCost (2*q+8) ≤ 288*(ssMulConst+1)*R^3 := band_rmul_le hw hR
  have hprep := bandAxisPrepCost_poly (S := ssMulConst+1) hR hS hw hk hsteps hN hMul
  have hpow : R^3 ≤ R^6 := Nat.pow_le_pow_right hR (by decide)
  change _ ≤ (1000000+10000000*(ssMulConst+1))*R^6
  nlinarith only [hheader,hprep,hpow]

end IntegerMultBounds.MathlibTM2.Cost
