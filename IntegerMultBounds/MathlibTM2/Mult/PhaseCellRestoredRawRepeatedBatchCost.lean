module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredRawRepeatedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRepeatedBatchCost

/-! The restored replica caller pays RHS retirement per output coordinate.
Increasing the replica count repeats neither numerical setup nor retained headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.NLogN

def restoredRawRepeatedBatchCoordinateCost (p l target rhsExp : ℕ) : ℕ :=
  rawRepeatedBatchCoordinateCost p l target rhsExp+12*executionWidth p l target rhsExp

def restoredRawRepeatedBatchCellCost (p l s target rhsExp : ℕ) : ℕ :=
  rawRepeatedBatchCellCost p l s target rhsExp+15

theorem restoredRawRepeatedBatchCost_eq (p l B L s t u target rhsExp lo : ℕ) :
    restoredRawRepeatedBatchCost p l (B+1) L s t u target rhsExp lo =
      restoredRawRepeatedBatchCost p l 1 L s t u target rhsExp lo+
        (B*L)*restoredRawRepeatedBatchCoordinateCost p l target rhsExp+
        B*restoredRawRepeatedBatchCellCost p l s target rhsExp := by
  unfold restoredRawRepeatedBatchCost
  rw [rawRepeatedBatchCost_eq p l B]
  unfold restoredRawRepeatedBatchCoordinateCost restoredRawRepeatedBatchCellCost
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
