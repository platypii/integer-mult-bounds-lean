module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRepeatedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatedBatchCost

/-! The executed raw replica caller has one numerical setup. Its per-replica
ledger separates coordinate arithmetic from the full-source gathering scan. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

def rawRepeatedBatchCoordinateCost (p l target rhsExp : ℕ) : ℕ :=
  repeatedBatchCoordinateCost p l target rhsExp+14*executionWidth p l target rhsExp

def rawRepeatedBatchCellCost (p l s target rhsExp : ℕ) : ℕ :=
  repeatedBatchCellCost p l target rhsExp+36*s*executionWidth p l target rhsExp+15*s+52

theorem rawReplicaGatherCost_affine (q s lo L B : ℕ) :
    rawReplicaGatherCost q s lo L B = rawReplicaGatherCost q s lo L 0+
      B*(14*L*(2*q+8)+36*s*(2*q+8)+15*s+52) := by
  simp only [rawReplicaGatherCost,generateReplicaControlsCost]
  ring

/-- Increasing the replica count repeats neither table exponentials nor inverse setup. -/
theorem rawRepeatedBatchCost_eq (p l B L s t u target rhsExp lo : ℕ) :
    rawRepeatedBatchCost p l (B+1) L s t u target rhsExp lo =
      rawRepeatedBatchCost p l 1 L s t u target rhsExp lo+
        (B*L)*rawRepeatedBatchCoordinateCost p l target rhsExp+
        B*rawRepeatedBatchCellCost p l s target rhsExp := by
  have hw : 2*executionPrecision p l target rhsExp+8 = executionWidth p l target rhsExp := by
    unfold executionPrecision executionWidth
    omega
  simp only [rawRepeatedBatchCost,Nat.add_sub_cancel,Nat.sub_self]
  rw [rawReplicaGatherCost_affine]
  rw [repeatedClosedBatchCost_eq p l (B+1),repeatedClosedBatchCost_eq p l 1]
  simp only [rawRepeatedBatchCoordinateCost,rawRepeatedBatchCellCost,hw]
  ring

/-- The full ambient scan is explicit in the raw caller's bound. It is not
absorbed into the shared numerical setup. -/
theorem rawRepeatedBatchCost_le_volume (p l B L s t u target rhsExp lo : ℕ)
    (hB : 0 < B) (hL : 0 < L) (hspan : lo+L ≤ s) :
    rawRepeatedBatchCost p l B L s t u target rhsExp lo ≤
      repeatedClosedBatchCost p l 0 L s t u target rhsExp lo+
        (B*L)*repeatedBatchCoordinateCost p l target rhsExp+
        B*repeatedBatchCellCost p l target rhsExp+250*(B*s*executionWidth p l target rhsExp) := by
  have hw : 2*executionPrecision p l target rhsExp+8 = executionWidth p l target rhsExp := by
    unfold executionPrecision executionWidth
    omega
  have he : B-1+1 = B := by omega
  have hg := rawReplicaGatherCost_le (executionPrecision p l target rhsExp) s lo L (B-1) hL hspan
  rw [he,hw] at hg
  unfold rawRepeatedBatchCost
  rw [repeatedClosedBatchCost_eq]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
