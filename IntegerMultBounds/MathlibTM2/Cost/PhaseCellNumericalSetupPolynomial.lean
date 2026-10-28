module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderGeneratorSetup
public import IntegerMultBounds.MathlibTM2.Cost.MatchBandLoad

/-! Polynomial construction bounds for the actual generated inverse pages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem scalarPrepareCost_le (w : ℕ) (hw : 1 ≤ w) : prepareCost 0 w ≤ 20000*w^3 := by
  have hsize : Nat.size (2*w) ≤ 2*w := Nat.size_le.mpr Nat.lt_two_pow_self
  have htop := (Schoenhage.Schedule.topN_facts hw).2.1
  have hbank : chirpBankLoadCost bank bankInput w w (inputBits w) = 42*w+49 := by
    simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments,bankInput,inputBits,
      List.ofFn_succ]
    ring
  have hsq : w ≤ w^2 := by nlinarith only [hw]
  have hcub : w^2 ≤ w^3 := by nlinarith only [hw,Nat.mul_le_mul_left (w^2) hw]
  unfold prepareCost counterSetupCost
  rw [hbank]
  unfold chirpMultiplierSetupCost tblC
  nlinarith only [hsize,htop,hw,hsq,hcub,Nat.mul_le_mul_right (32*(w+4)^2+8*w) hsize]

theorem numericalGeneratorSetupCost_poly {P M L q V W Z : ℕ}
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hM : M ≤ Z) (hL : L ≤ Z)
    (hq : q ≤ Z) (hV : V ≤ Z) (hW : W ≤ Z) (hw : 1 ≤ W) :
    numericalGeneratorSetupCost P M L q V W ≤
      1000000*(ssMulConst+1)*Z^6 := by
  have hmul := band_rmul_le hW hZ
  have hprepare := scalarPrepareCost_le W hw
  have hprepare' : prepareCost 0 W ≤ 20000*Z^3 :=
    hprepare.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW 3))
  have htable : tblC V W ≤ 808*Z^2 := by
    have hwidth : V+4 ≤ 5*Z := by omega
    have hs := Nat.pow_le_pow_left hwidth 2
    have hsq : Z ≤ Z^2 := by nlinarith only [hZ]
    unfold tblC
    nlinarith only [hs,hW,hsq]
  have hsub : L-1 ≤ Z := (Nat.sub_le _ _).trans hL
  have hbound : numericalGeneratorSetupCost P M L q V W ≤
      (Z*(310*Z+114)+(160*Z+450))*(808*Z^2)+14*(Z*Z)+126*Z+9*Z+141+
        (Z*(24*(Z*Z)+48*Z+6*Z+48+7)+6)+
        (20000*Z^3+Z*(16*(Z*Z*Z)+15*(Z*Z)+
          Z*(Z*(288*(ssMulConst+1)*Z^3+55*Z+30)+20*Z+73+28*Z+38)+21*Z+94+5)+
          Z*(30*Z+6*(2*Z+8)+32)+31*Z+6*Z+79+
          (Z*(16*(2*Z+8)+21)+4*Z+12*(2*Z+8)+4*Z+31)+
          (Z*(12*Z+128)+6*(2*Z+8)+4*Z+134))+
        (12*(Z*Z)+18*(Z*(2*Z+8))+18*Z+8*(2*Z+8)+4*Z+44) := by
    unfold numericalGeneratorSetupCost factorFactoryCost constructFactorPageCost factorRowStepCost
      generatorSetupCost integerIterationCost integerRowCost packGeneratorsCost
    gcongr
  have hpow2 : Z ≤ Z^2 := by nlinarith only [hZ]
  have hpow3 : Z^2 ≤ Z^3 := by nlinarith only [Nat.mul_le_mul_left (Z^2) hZ]
  have hpow4 : Z^3 ≤ Z^4 := by nlinarith only [Nat.mul_le_mul_left (Z^3) hZ]
  have hpow5 : Z^4 ≤ Z^5 := by nlinarith only [Nat.mul_le_mul_left (Z^4) hZ]
  have hpow6 : Z^5 ≤ Z^6 := by nlinarith only [Nat.mul_le_mul_left (Z^5) hZ]
  have hS : 1 ≤ ssMulConst+1 := by omega
  have hscaled := Nat.mul_le_mul_left (ssMulConst+1) hpow6
  nlinarith only [hbound,hZ,hpow2,hpow3,hpow4,hpow5,hpow6,hscaled,hS,
    Nat.mul_le_mul_left (ssMulConst+1) hpow2,
    Nat.mul_le_mul_left (ssMulConst+1) hpow3,
    Nat.mul_le_mul_left (ssMulConst+1) hpow4,
    Nat.mul_le_mul_left (ssMulConst+1) hpow5]

theorem headerGeneratorSetupCost_poly {P M q s t u band L Z : ℕ}
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hM : M ≤ Z) (hq : q ≤ Z) (hu : u ≤ Z) (hL : L ≤ Z)
    (hW : integerSetupWidth P q (M+1) 0 ≤ Z)
    (hV : coefficientWorkspaceWidth P (integerSetupWidth P q (M+1) 0) t u band L ≤ Z) :
    headerGeneratorSetupCost P M q s t u band L ≤
      100*(s+t+band)+(1000000*(ssMulConst+1)+10000)*Z^6 := by
  let W := integerSetupWidth P q (M+1) 0
  let V := coefficientWorkspaceWidth P W t u band L
  have hw : 1 ≤ W := by dsimp [W,integerSetupWidth]; omega
  have hnum := numericalGeneratorSetupCost_poly hZ hP hM hL hq hV hW hw
  have hPM := Nat.mul_le_mul hP hM
  have hpowers : Z ≤ Z^6 ∧ Z^2 ≤ Z^6 := by
    constructor
    · simpa using Nat.pow_le_pow_right hZ (show 1 ≤ 6 by decide)
    · exact Nat.pow_le_pow_right hZ (by decide)
  have hone : 1 ≤ Z^6 := Nat.one_le_pow _ _ hZ
  unfold headerGeneratorSetupCost coefficientWidthCost prepareCoefficientHeadersCost coefficientHeadersLinearCost
  change _ ≤ _ at hnum
  dsimp only [W,V] at *
  nlinarith only [hnum,hPM,hpowers.1,hpowers.2,hone,hP,hM,hq,hu,hL,hW,hV]

end IntegerMultBounds.MathlibTM2.Cost
