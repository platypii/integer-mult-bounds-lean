module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedConditionalHaloClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchCost

/-! Separate a halo class's shared setup, coordinate work and padded cell work.
Endpoint copies and releases are explicit shared charges. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def cachedHaloClassSharedCost (p l L s t u target rhsExp a b : ℕ) : ℕ :=
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let V := weightWorkspaceWidth P q w t u
  installHaloGroupHeadersCost P N q l s t u band a b L+
    haloOriginControlsSharedCost P q s t u band a b L+advanceControlsSharedCost V s w+
    (2*(P+N+q+l+s+t+u+band+3*L+a+b)+28)+
    (142*s*w+rawNaturalGatherCost q s+2*(a+b)+5+70)+discardBatchOriginsCost P q t u 0+cachedClosedBatchCost p l 0 L s t u target rhsExp+7+
    (6*L+19*V+17)

def cachedHaloClassCellCost (p l t u target rhsExp : ℕ) : ℕ :=
  let P := 2^15*p
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let V := weightWorkspaceWidth P q w t u
  cachedBatchCellCost p l target rhsExp+3*tblC V V+49*V+49

theorem cachedHaloClassCost_le (p l L s t u target rhsExp a b : ℕ) :
    let V := weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u
    let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
    (6*L+19*V+14)+cachedConditionalHaloClassCost p l L s t u target rhsExp a b+3 ≤
      cachedHaloClassSharedCost p l L s t u target rhsExp a b+
        (B*L)*cachedBatchCoordinateCost p l target rhsExp+B*cachedHaloClassCellCost p l t u target rhsExp := by
  dsimp only
  have hw : 2*executionPrecision p l target rhsExp+8 = executionWidth p l target rhsExp := by
    unfold executionPrecision executionWidth
    omega
  rw [cachedConditionalHaloClassCost]
  by_cases hB : 0 < (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
  · simp only [conditionalHaloGroupPreparationCost,probeAndGatherHaloControlsCost,
      generateHaloClassControlsCost,prepareHaloClassControlsCost,preparedHaloClassCost,preparedHaloAdvanceCost,
      cachedProtectedControlledHaloClassCost,cachedBatchFromOriginsCost,discardBatchOriginsCost,hB,ite_eq_left,cachedHaloClassSharedCost,
      haloOriginControlsSharedCost,advanceControlsSharedCost,cachedHaloClassCellCost]
    rw [cachedClosedBatchCost_eq]
    simp only [hw]
    ring_nf
    omega
  · have hz : (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length = 0 := by omega
    simp only [conditionalHaloGroupPreparationCost,probeAndGatherHaloControlsCost,
      generateHaloClassControlsCost,prepareHaloClassControlsCost,preparedHaloClassCost,
      cachedHaloClassSharedCost,haloOriginControlsSharedCost,advanceControlsSharedCost,
      cachedHaloClassCellCost,discardBatchOriginsCost,hz,Nat.zero_mul,Nat.add_zero,Nat.lt_irrefl,↓reduceIte]
    simp only [hw]
    ring_nf
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
