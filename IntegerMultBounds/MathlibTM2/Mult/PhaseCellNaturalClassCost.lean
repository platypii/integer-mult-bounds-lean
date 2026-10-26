module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchCostAffine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalNaturalClass

/-! Separate one runtime class's shared control/setup cost from its exact
coordinate and cell charges. Empty classes retain only their paid setup bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def originControlsSharedCost (P q s t u band L : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  4*q+5+weightWidthCost P q w t u+104*V+137+originHeadersCost s t band L V+
    (27*(t-s+1)+9)*tblC V V+6+62*V+63+2*(w+V)+5

def advanceControlsSharedCost (V s w : ℕ) : ℕ :=
  (32*V+41)+(w*(4*V+10)+6*V+10)+8*s*w+11+(38*V+39)

def naturalClassSharedCost (p l L s t u target rhsExp : ℕ) : ℕ :=
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let V := weightWorkspaceWidth P q w t u
  installGroupHeadersCost P N q l s t u band L+
    originControlsSharedCost P q s t u band L+advanceControlsSharedCost V s w+
    (2*(P+N+q+l+s+t+u+band+3*L)+23)+
    (142*s*w+rawNaturalGatherCost q s+70)+sizedClosedBatchBound p l 0 L s t u target rhsExp+7+
    (6*L+19*V+17)

def naturalClassCellCost (p l t u target rhsExp : ℕ) : ℕ :=
  let P := 2^15*p
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let V := weightWorkspaceWidth P q w t u
  batchCellCost p l t u target rhsExp+3*tblC V V+37*V+40

theorem naturalClassCost_le (p l L s t u target rhsExp : ℕ) :
    let V := weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u
    let B := (naturalLengthGroup s t (PhaseCellBand.width p u) L).length
    (6*L+19*V+14)+conditionalNaturalClassCost p l L s t u target rhsExp+3 ≤
      naturalClassSharedCost p l L s t u target rhsExp+
        (B*L)*batchCoordinateCost p l t u target rhsExp+B*naturalClassCellCost p l t u target rhsExp := by
  dsimp only
  have hw : 2*executionPrecision p l target rhsExp+8 = executionWidth p l target rhsExp := by
    unfold executionPrecision executionWidth
    omega
  rw [conditionalNaturalClassCost]
  by_cases hB : 0 < (naturalLengthGroup s t (PhaseCellBand.width p u) L).length
  · simp only [conditionalGroupPreparationCost,probeAndGatherControlsCost,
      generateOriginControlsCost,unaryOriginControllerCost,preparedNaturalAdvanceCost,
      protectedControlledClassCost,hB,ite_eq_left,naturalClassSharedCost,
      originControlsSharedCost,advanceControlsSharedCost,naturalClassCellCost]
    rw [sizedClosedBatchBound_eq]
    simp only [hw]
    ring_nf
    omega
  · have hz : (naturalLengthGroup s t (PhaseCellBand.width p u) L).length = 0 := by omega
    simp only [conditionalGroupPreparationCost,probeAndGatherControlsCost,
      generateOriginControlsCost,unaryOriginControllerCost,
      naturalClassSharedCost,originControlsSharedCost,advanceControlsSharedCost,
      naturalClassCellCost,hz,Nat.zero_mul,Nat.add_zero,Nat.lt_irrefl,↓reduceIte]
    simp only [hw]
    ring_nf
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
