module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStagedStock

/-! Exact shared/per-cell decomposition of the executed numerical workspace.
The per-cell coefficient contains no scalar multiplication scratch reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

def stagedCellStockPerCell (R cExp e l w L : ℕ) : ℕ :=
  1852*L*w+12*L*(cExp+e+2*l+3)+1068*L+1857+
    (7368*(R+1)+696)*(2^l*w)

theorem stagedCellWorkspace_affine (R K q cExp e l w M L : ℕ) :
    stagedCellWorkspace R K q cExp e l w M L =
      stagedCellWorkspace R K q cExp e l w 0 L + M*stagedCellStockPerCell R cExp e l w L := by
  simp only [stagedCellWorkspace,publishedCellWorkspace,cellArithmeticWorkspace,
    normalizedInteriorWorkspace,inputInteriorWorkspace,inputStageWorkspace,interiorWorkspace,
    compactPairWorkspace,triangularPairWorkspace,Fixed.workspace,
    applyWorkspace,runWorkspace,realScalarWorkspace,applyWeightsWorkspace,runWeightsWorkspace,
    realWeightWorkspace,preparedOutputWorkspace,outputFromHeadersWorkspace,closedOutputWorkspace,
    stagePayloadCost,fetchPageCost,publishFromDimensionsCost,installInputCost,
    fixedMergeCost,fetchScalarCost,routeCost,routeWeightsCost,pairFinishCost,
    fetchOutputTableCost,scaleOutputPrefixCost,stagedCellStockPerCell]
  ring

/-- Repeated stock is linear encoded/padded traffic, with no multiplication-time factor. -/
theorem stagedCellStockPerCell_le (R cExp e l w L : ℕ) (hL : 1 ≤ L) (hw : 1 ≤ w)
    (hshift : cExp+e+2*l+3 ≤ w) :
    stagedCellStockPerCell R cExp e l w L ≤ 8064*(R+1)*(L+2^l)*w := by
  have hs := Nat.mul_le_mul_left (12*L) hshift
  have hl : L ≤ L*w := Nat.le_mul_of_pos_right _ hw
  have hv : 1 ≤ L*w := Nat.mul_le_mul hL hw
  have hbase : stagedCellStockPerCell R cExp e l w L ≤
      4789*(L*w)+(7368*(R+1)+696)*(2^l*w) := by
    unfold stagedCellStockPerCell
    nlinarith only [hs,hl,hv]
  calc
    _ ≤ 4789*(L*w)+(7368*(R+1)+696)*(2^l*w) := hbase
    _ ≤ (8064*(R+1))*(L*w)+(8064*(R+1))*(2^l*w) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
        (Nat.mul_le_mul_right _ (by omega))
    _ = _ := by ring

theorem stagedCellWorkspace_le_shared_add_traffic (R K q cExp e l w M L : ℕ)
    (hL : 1 ≤ L) (hw : 1 ≤ w) (hshift : cExp+e+2*l+3 ≤ w) :
    stagedCellWorkspace R K q cExp e l w M L ≤
      stagedCellWorkspace R K q cExp e l w 0 L+8064*(R+1)*M*(L+2^l)*w := by
  rw [stagedCellWorkspace_affine]
  have hs := Nat.mul_le_mul_left M (stagedCellStockPerCell_le R cExp e l w L hL hw hshift)
  nlinarith only [hs]

end IntegerMultBounds.MathlibTM2.Cost
