module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolveReplicaHaloInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloLoopCost

/-! Initialization, endpoint borrowing and final release are paid in the closed
replica caller. Their per-replica overhead does not repeat numerical setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem solveReplicaHaloInteriorCost_eq {s t : ℕ} [NeZero s] (hst : s < t)
    (p l B u target rhsExp a b : ℕ) :
    let band := PhaseCellBand.width p u
    solveReplicaHaloInteriorCost p l (B+1) s t u target rhsExp a b =
      solveReplicaHaloInteriorCost p l 1 s t u target rhsExp a b+
        (B*(haloInterior s t band a b).card)*restoredRawRepeatedBatchCoordinateCost p l target rhsExp+
        (B*(haloCellPhases s t band a b).length)*(restoredRawRepeatedBatchCellCost p l s target rhsExp+4)+
        6*B := by
  dsimp only [solveReplicaHaloInteriorCost]
  rw [replicaHaloLoopCost_eq hst]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
