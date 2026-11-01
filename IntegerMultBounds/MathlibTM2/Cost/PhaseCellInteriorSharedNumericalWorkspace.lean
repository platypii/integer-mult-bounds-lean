module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRingSharedWorkspacePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryNumericalWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellNumericalStock

/-! Zero-replica numerical scratch is a shared polynomial reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem stagedCellWorkspace_zero_poly {R K q cExp e l w L Z : ℕ} (hZ : 1 ≤ Z)
    (hR : R ≤ Z) (hK : K ≤ Z) (hqpos : 1 ≤ q) (hlq : l ≤ q) (hwq : w ≤ 10*q)
    (hwpos : 1 ≤ w) (hw : w ≤ Z) (hL : L ≤ Z) (hr : 2^l ≤ Z)
    (hprecision : q+cExp+e+2*l+3 ≤ Z) :
    stagedCellWorkspace R K q cExp e l w 0 L ≤
      (4*ringSharedWorkspaceConstant+1000000*(ssMulConst+1))*Z^11 := by
  have hq : q ≤ Z := by omega
  have hl : l ≤ Z := by omega
  have hf := fixedWorkspace_zero_poly hZ hR hqpos hlq hwq hq hl hw hr
  have hp := scalarPrepareCost_arg_le hq hw hwpos
  have hp' := scalarPrepareCost_arg_le (show q+(cExp+e+1) ≤ Z by omega) hw hwpos
  have hs := realScalarWorkspace_poly hZ hK hw (show 0 ≤ Z by omega)
  have hw' := realWeightWorkspace_poly hZ hK hw (show 0 ≤ Z by omega)
  have hLw := Nat.mul_le_mul hL hw
  have hrw := Nat.mul_le_mul hr hw
  have h3 : Z^3 ≤ Z^11 := Nat.pow_le_pow_right hZ (by decide)
  have h4 : Z^4 ≤ Z^11 := Nat.pow_le_pow_right hZ (by decide)
  have h2 : Z^2 ≤ Z^11 := Nat.pow_le_pow_right hZ (by decide)
  have h1 : Z ≤ Z^11 := Nat.le_self_pow (by decide) Z
  have h0 : 1 ≤ Z^11 := Nat.one_le_pow _ _ hZ
  have hscale := Nat.mul_le_mul_left (ssMulConst+1) h4
  have hscale0 : Z^11 ≤ (ssMulConst+1)*Z^11 := Nat.le_mul_of_pos_left _ (by omega)
  simp only [stagedCellWorkspace,publishedCellWorkspace,cellArithmeticWorkspace,
    normalizedInteriorWorkspace,inputInteriorWorkspace,inputStageWorkspace,interiorWorkspace,
    compactPairWorkspace,triangularPairWorkspace,applyWorkspace,runWorkspace,
    applyWeightsWorkspace,runWeightsWorkspace,preparedOutputWorkspace,outputFromHeadersWorkspace,
    closedOutputWorkspace,stagePayloadCost,fetchPageCost,publishFromDimensionsCost,
    installInputCost,fixedMergeCost,fetchScalarCost,routeCost,routeWeightsCost,pairFinishCost,
    fetchOutputTableCost,scaleOutputPrefixCost,prepareWeightsCost,
    Nat.zero_mul,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
  nlinarith only [hf,hp,hp',hs,hw',h3,h4,h2,h1,h0,hscale,hscale0,hprecision,hw,hL,hLw,hrw]

end IntegerMultBounds.MathlibTM2.Cost
