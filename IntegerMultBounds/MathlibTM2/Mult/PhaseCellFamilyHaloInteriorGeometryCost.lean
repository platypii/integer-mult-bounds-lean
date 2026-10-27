module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilySolveHaloInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedHaloClassGeometryCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloInteriorCost

/-! The retained-family pass charges coordinate work to the actual interior,
cell work to the clipped phase count, and shared controls to six candidates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def familyHaloInteriorGeometryCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let V := weightWorkspaceWidth P q w t u
  initializeHaloLengthKeysBound P N q l s t u band a b+
    ((haloLengthCandidates s t band a b).map (fun L =>
      cachedHaloClassSharedCost p l L s t u target rhsExp a b)).sum+
    (haloInterior s t band a b).card*(cachedBatchCoordinateCost p l target rhsExp+44*w)+
    (t-s+1)*cachedHaloClassCellCost p l t u target rhsExp+2*(V+w)+207

theorem familySolveHaloInteriorCost_geometry_le {s t : ℕ} [NeZero s]
    (hst : s < t) (A p l u target rhsExp a b : ℕ) :
    familySolveHaloInteriorCost A p l s t u target rhsExp a b ≤
      familyHaloInteriorGeometryCost p l s t u target rhsExp a b := by
  let band := PhaseCellBand.width p u
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let V := weightWorkspaceWidth (2^15*p) q w t u
  let keys := haloLengthKeys s t band a b
  have hc := List.sum_le_sum (l := keys) (fun L _ => by
    have h := cachedHaloClassCost_le p l L s t u target rhsExp a b
    exact (Nat.le_add_right _ 3).trans h)
  have hs := haloLengthKeys_cost_le hst band a b
    (fun L => cachedHaloClassSharedCost p l L s t u target rhsExp a b)
    (cachedBatchCoordinateCost p l target rhsExp) (cachedHaloClassCellCost p l t u target rhsExp)
  have hi := initializeHaloLengthKeysCost_le (2^15*p) (executionStagePrecision p l target rhsExp+1)
    q l s t u band a b
  have hk : keys.length ≤ 6 := haloLengthKeys_length_le s t band a b
  have he := familyHaloLengthKeyLoopCost_eq A p l s t u target rhsExp V a b keys
  rw [haloLengthKeys_volume hst] at he
  change _ ≤ ((haloLengthKeys s t band a b).map _).sum at hc
  have hsum := hc.trans hs
  dsimp only [familySolveHaloInteriorCost,familyHaloInteriorGeometryCost]
  dsimp only [keys,band,q,w,V] at hi hk he hsum
  nlinarith only [hi,hk,he,hsum]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
