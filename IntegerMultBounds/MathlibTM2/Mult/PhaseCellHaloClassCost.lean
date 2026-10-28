module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalClassCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalHaloClass

/-! Separate a halo class's shared setup, coordinate work and padded cell work.
Endpoint copies and releases are explicit shared charges. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloControlCellCost (P q w t u : ℕ) : ℕ :=
  let G := haloGeometryWidth t w
  let V := weightWorkspaceWidth P q w t u
  3*tblC G G+47*G+10*V+59

def haloOriginControlsSharedCost (P q s t u band a b L : ℕ) : ℕ :=
  let w := 2*q+8
  let G := haloGeometryWidth t w
  let V := weightWorkspaceWidth P q w t u
  4*q+5+generateHaloGeometryWidthCost t w+104*G+137+haloClassHeadersCost s t band a b L G+
    (36*(t-s+1)+9)*tblC G G+6+62*G+63+2*(w+G)+5+
    weightWidthCost P q w t u+4*G+4*V+14

def haloClassCellCost (p l t u target rhsExp : ℕ) : ℕ :=
  let P := 2^15*p
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  batchCellCost p l t u target rhsExp+haloControlCellCost P q w t u+4

def haloClassSharedCost (p l L s t u target rhsExp a b : ℕ) : ℕ :=
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let V := weightWorkspaceWidth P q w t u
  installHaloGroupHeadersCost P N q l s t u band a b L+
    haloOriginControlsSharedCost P q s t u band a b L+advanceControlsSharedCost (haloGeometryWidth t w) s w+
    (2*(P+N+q+l+s+t+u+band+3*L+a+b)+28)+
    (142*s*w+rawNaturalGatherCost q s+2*(a+b)+5+70)+sizedClosedBatchBound p l 0 L s t u target rhsExp+7+
    (6*L+19*V+17)

theorem haloClassCost_le (p l L s t u target rhsExp a b : ℕ) :
    let V := weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u
    let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
    (6*L+19*V+14)+conditionalHaloClassCost p l L s t u target rhsExp a b+3 ≤
      haloClassSharedCost p l L s t u target rhsExp a b+
        (B*L)*batchCoordinateCost p l t u target rhsExp+B*haloClassCellCost p l t u target rhsExp := by
  dsimp only
  have hw : 2*executionPrecision p l target rhsExp+8 = executionWidth p l target rhsExp := by
    unfold executionPrecision executionWidth
    omega
  rw [conditionalHaloClassCost]
  by_cases hB : 0 < (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
  · simp only [conditionalHaloGroupPreparationCost,probeAndGatherHaloControlsCost,
      probeGeometryHaloGatherCost,prepareGeometryHaloClassControlsCost,completeGeometryHaloGatherCost,
      widenGeometryOriginsCost,preparedHaloClassCost,preparedHaloAdvanceCost,
      protectedControlledHaloClassCost,hB,ite_eq_left,haloClassSharedCost,
      haloOriginControlsSharedCost,advanceControlsSharedCost,haloClassCellCost,haloControlCellCost]
    rw [sizedClosedBatchBound_eq]
    simp only [hw]
    ring_nf
    omega
  · have hz : (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length = 0 := by omega
    simp only [conditionalHaloGroupPreparationCost,probeAndGatherHaloControlsCost,
      probeGeometryHaloGatherCost,prepareGeometryHaloClassControlsCost,completeGeometryHaloGatherCost,
      widenGeometryOriginsCost,preparedHaloClassCost,preparedHaloAdvanceCost,
      haloClassSharedCost,haloOriginControlsSharedCost,advanceControlsSharedCost,
      haloClassCellCost,hz,Nat.zero_mul,Nat.add_zero,Nat.lt_irrefl,↓reduceIte]
    simp only [hw]
    ring_nf
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
