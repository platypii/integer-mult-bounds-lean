module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunPreparedPacketCouplingRowsStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryNumericalWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCouplingSetupPolynomial

/-! One packet-coupling row's scratch is shared by the entire column stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {P₀ U : Type}

theorem runPreparedPacketCouplingRowsWorkspace_poly {K P q w s t u band Z : ℕ}
    (hZ : 1 ≤ Z) (hK : K ≤ Z) (hP : P ≤ Z) (hq : q ≤ Z) (hw : w ≤ Z) (hwpos : 1 ≤ w)
    (hs : s ≤ Z) (hb : band ≤ Z) (hrows : 2*band+1 ≤ Z)
    (hV : liftedCoefficientWidth P q w s t u band ≤ Z)
    (hpacket : packetCoefficientPush (Q := Q) (A := A) (U := U) ≤ Z)
    (hzero : zeroPacketSpatialCouplingRowPush (P₀ := P₀) (Q := Q) (A := A) (U := U) ≤ Z) :
    runPreparedPacketCouplingRowsWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) K P q w s t u band ≤
      3000000*(ssMulConst+1)*Z^5 := by
  have hcoeff := couplingCoefficientPageRowCost_poly hZ hP hw hb hV false
  have hmarked : markedRowCoefficientCost P q (liftedCoefficientWidth P q w s t u band) w band ≤
      2000000*Z^4 := by
    dsimp only [couplingCoefficientPageRowCost,prepareCouplingCoefficientRowCost] at hcoeff
    simp only [Bool.false_eq_true,ite_false] at hcoeff
    omega
  have hmarkedScaled := Nat.mul_le_mul hpacket hmarked
  have hblank : zeroPacketSpatialCouplingRowCost P q w s t u band ≤ 67*Z := by
    unfold zeroPacketSpatialCouplingRowCost
    omega
  have hblankScaled := Nat.mul_le_mul hzero hblank
  have hprepare := scalarPrepareCost_arg_le hq hw hwpos
  have hweight := realWeightWorkspace_poly hZ hK hw hrows
  have hinput : prepareCountedCouplingInputsCost band w ≤ 4*Z+5+(Z*(16*Z+9)+16) := by
    unfold prepareCountedCouplingInputsCost copyCountedLineCost
    gcongr
  have hvolume := Nat.mul_le_mul hs hw
  have hrowVolume := Nat.mul_le_mul (show 2*band+1+1 ≤ Z+1 by omega) (show w+1 ≤ Z+1 by omega)
  have h₄ : Z^4 ≤ Z^5 := Nat.pow_le_pow_right hZ (by decide)
  have h₃ : Z^3 ≤ Z^5 := Nat.pow_le_pow_right hZ (by decide)
  have h₂ : Z^2 ≤ Z^5 := Nat.pow_le_pow_right hZ (by decide)
  have h₁ : Z ≤ Z^5 := Nat.le_self_pow (by decide) Z
  have h₀ : 1 ≤ Z^5 := Nat.one_le_pow _ _ hZ
  have hscale : Z^5 ≤ (ssMulConst+1)*Z^5 := Nat.le_mul_of_pos_left _ (by omega)
  have hscale₄ := Nat.mul_le_mul_left (ssMulConst+1) h₄
  unfold runPreparedPacketCouplingRowsWorkspace packetSpatialCouplingRowStepWorkspace
    guardedPacketSpatialCouplingRowWorkspace packetSpatialCouplingRowWorkspace
    generatedReadyRowWorkspace transferCountedLineCost
  nlinarith only [hmarkedScaled,hblankScaled,hprepare,hweight,hinput,hvolume,hrowVolume,
    hq,hw,hs,hb,hrows,hV,h₄,h₃,h₂,h₁,h₀,hscale,hscale₄]

end IntegerMultBounds.MathlibTM2.Cost
