module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolveHaloInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassCost
public import IntegerMultBounds.NLogN.PhaseCellHaloScheduleCost

/-! A clipped-interior ledger with six candidate setups, exact interior-coordinate
volume and at most one padded cell charge per natural phase. No setup is repaid
per cell, and no class-count factor multiplies the repeated work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def initializeHaloLengthKeysBound (P N q l s t u band a b : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  installHaloGroupHeadersCost P N q l s t u band a b 0+prepareHaloLengthKeysCost P q s t u band a b+
    30*V+6*w+2*(P+N+q+l+s+t+u+band+a+b)+57

theorem initializeHaloLengthKeysCost_le (P N q l s t u band a b : ℕ) :
    initializeHaloLengthKeysCost P N q l s t u band a b ≤ initializeHaloLengthKeysBound P N q l s t u band a b := by
  have hK := haloLengthKeys_length_le s t band a b
  have hKV := Nat.mul_le_mul_right (weightWorkspaceWidth P q (2*q+8) t u) hK
  dsimp only [initializeHaloLengthKeysCost,initializeHaloLengthKeysBound]
  nlinarith only [hK,hKV]

def haloInteriorCostBound (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let V := weightWorkspaceWidth P q w t u
  initializeHaloLengthKeysBound P N q l s t u band a b+
    ((haloLengthCandidates s t band a b).map (fun L => haloClassSharedCost p l L s t u target rhsExp a b)).sum+
    (haloInterior s t band a b).card*batchCoordinateCost p l t u target rhsExp+
    (t-s+1)*haloClassCellCost p l t u target rhsExp+2+(2*(V+w)+5)

theorem haloLengthKeyLoopCost_le {s t : ℕ} [NeZero s] (hst : s < t) (p l u target rhsExp a b : ℕ) :
    let band := PhaseCellBand.width p u
    let V := weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u
    haloLengthKeyLoopCost p l s t u target rhsExp V a b (haloLengthKeys s t band a b)+1 ≤
      ((haloLengthCandidates s t band a b).map (fun L => haloClassSharedCost p l L s t u target rhsExp a b)).sum+
        (haloInterior s t band a b).card*batchCoordinateCost p l t u target rhsExp+
        (t-s+1)*haloClassCellCost p l t u target rhsExp+2 := by
  dsimp only
  have hc := List.sum_le_sum (l := haloLengthKeys s t (PhaseCellBand.width p u) a b)
    (fun L _ => haloClassCost_le p l L s t u target rhsExp a b)
  have hs := haloLengthKeys_cost_le hst (PhaseCellBand.width p u) a b
    (fun L => haloClassSharedCost p l L s t u target rhsExp a b)
    (batchCoordinateCost p l t u target rhsExp) (haloClassCellCost p l t u target rhsExp)
  dsimp only [haloLengthKeyLoopCost]
  omega

/-- The cost of the actual initialized solver obeys the geometry-separated ledger. -/
theorem solveHaloInteriorCost_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p l u target rhsExp a b : ℕ) :
    solveHaloInteriorCost p l s t u target rhsExp a b ≤ haloInteriorCostBound p l s t u target rhsExp a b := by
  have hi := initializeHaloLengthKeysCost_le (2^15*p) (executionStagePrecision p l target rhsExp+1)
    (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b
  have hl := haloLengthKeyLoopCost_le hst p l u target rhsExp a b
  dsimp only [solveHaloInteriorCost,haloInteriorCostBound]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
