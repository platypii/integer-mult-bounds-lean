module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolveNaturalInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalClassCost
public import IntegerMultBounds.NLogN.PhaseCellNaturalScheduleCost

/-! A whole-interior ledger with four candidate setups, exact interior-coordinate
volume and at most one padded cell charge per natural phase. No setup is repaid
per cell, and no class-count factor multiplies the repeated work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def initializeLengthKeysBound (P N q l s t u band : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  installGroupHeadersCost P N q l s t u band 0+preparePositiveLengthKeysCost P q s t u band+
    22*V+6*w+2*(P+N+q+l+s+t+u+band)+48

theorem initializeLengthKeysCost_le (P N q l s t u band : ℕ) :
    initializeLengthKeysCost P N q l s t u band ≤ initializeLengthKeysBound P N q l s t u band := by
  have hK := naturalPositiveLengthKeys_length_le s t band
  have hKV := Nat.mul_le_mul_right (weightWorkspaceWidth P q (2*q+8) t u) hK
  dsimp only [initializeLengthKeysCost,initializeLengthKeysBound]
  nlinarith only [hK,hKV]

def naturalInteriorCostBound (p l s t u target rhsExp : ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let V := weightWorkspaceWidth P q w t u
  initializeLengthKeysBound P N q l s t u band+
    ((naturalLengthCandidates s t band).map (fun L => naturalClassSharedCost p l L s t u target rhsExp)).sum+
    (interiorSet s t band).card*batchCoordinateCost p l t u target rhsExp+
    (t-s+1)*naturalClassCellCost p l t u target rhsExp+2+(2*(V+w)+5)

theorem lengthKeyLoopCost_le {s t : ℕ} [NeZero s] (hst : s < t) (p l u target rhsExp : ℕ) :
    let band := PhaseCellBand.width p u
    let V := weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u
    lengthKeyLoopCost p l s t u target rhsExp V (naturalPositiveLengthKeys s t band)+1 ≤
      ((naturalLengthCandidates s t band).map (fun L => naturalClassSharedCost p l L s t u target rhsExp)).sum+
        (interiorSet s t band).card*batchCoordinateCost p l t u target rhsExp+
        (t-s+1)*naturalClassCellCost p l t u target rhsExp+2 := by
  dsimp only
  have hc := List.sum_le_sum (l := naturalPositiveLengthKeys s t (PhaseCellBand.width p u))
    (fun L _ => naturalClassCost_le p l L s t u target rhsExp)
  have hs := naturalPositiveLengthKeys_cost_le hst (PhaseCellBand.width p u)
    (fun L => naturalClassSharedCost p l L s t u target rhsExp)
    (batchCoordinateCost p l t u target rhsExp) (naturalClassCellCost p l t u target rhsExp)
  dsimp only [lengthKeyLoopCost]
  omega

/-- The cost of the actual initialized solver obeys the geometry-separated ledger. -/
theorem solveNaturalInteriorCost_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p l u target rhsExp : ℕ) :
    solveNaturalInteriorCost p l s t u target rhsExp ≤ naturalInteriorCostBound p l s t u target rhsExp := by
  have hi := initializeLengthKeysCost_le (2^15*p) (executionStagePrecision p l target rhsExp+1)
    (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u)
  have hl := lengthKeyLoopCost_le hst p l u target rhsExp
  dsimp only [solveNaturalInteriorCost,naturalInteriorCostBound]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
