module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProcessReplicaCell
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredRawRepeatedBatchCost

/-! Descriptor decoding, private header copies and cleanup have an explicit
ledger. Each added replica pays arithmetic and its count copies, without setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.NLogN

theorem retainedRawRepeatedBatchCost_eq (p l B L s t u target rhsExp lo : ℕ) :
    retainedRawRepeatedBatchCost p l (B+1) L s t u target rhsExp lo =
      retainedRawRepeatedBatchCost p l 1 L s t u target rhsExp lo+
        (B*L)*restoredRawRepeatedBatchCoordinateCost p l target rhsExp+
        B*(restoredRawRepeatedBatchCellCost p l s target rhsExp+4) := by
  unfold retainedRawRepeatedBatchCost
  rw [restoredRawRepeatedBatchCost_eq p l B]
  ring

theorem processReplicaCellCost_eq (p l B L s t u target rhsExp V lo : ℕ) :
    processReplicaCellCost p l (B+1) L s t u target rhsExp V lo =
      processReplicaCellCost p l 1 L s t u target rhsExp V lo+
        (B*L)*restoredRawRepeatedBatchCoordinateCost p l target rhsExp+
        B*(restoredRawRepeatedBatchCellCost p l s target rhsExp+4) := by
  unfold processReplicaCellCost
  rw [retainedRawRepeatedBatchCost_eq p l B]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
