module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunReplicaHaloCells
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProcessReplicaCellCost

/-! The executed descriptor loop pays one setup per generated phase, with
replica arithmetic charged by the exact selected interior volume. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem replicaHaloLoopCost_eq {s t : ℕ} [NeZero s] (hst : s < t)
    (p l B u target rhsExp V a b : ℕ) :
    let band := PhaseCellBand.width p u
    let phases := haloCellPhases s t band a b
    replicaHaloLoopCost p l (B+1) s t u target rhsExp V a b phases =
      replicaHaloLoopCost p l 1 s t u target rhsExp V a b phases+
        (B*(haloInterior s t band a b).card)*restoredRawRepeatedBatchCoordinateCost p l target rhsExp+
        (B*phases.length)*(restoredRawRepeatedBatchCellCost p l s target rhsExp+4) := by
  dsimp only
  let band := PhaseCellBand.width p u
  have hsum (phases : List ℕ) :
      (phases.map (fun phase => processReplicaCellCost p l (B+1) (haloLength s t band a b phase)
        s t u target rhsExp V (haloStart s t band a phase)+3)).sum =
      (phases.map (fun phase => processReplicaCellCost p l 1 (haloLength s t band a b phase)
        s t u target rhsExp V (haloStart s t band a phase)+3)).sum+
        (B*(phases.map (haloLength s t band a b)).sum)*restoredRawRepeatedBatchCoordinateCost p l target rhsExp+
        (B*phases.length)*(restoredRawRepeatedBatchCellCost p l s target rhsExp+4) := by
    induction phases with
    | nil => simp
    | cons phase phases ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      rw [processReplicaCellCost_eq,ih]
      ring
  dsimp only [replicaHaloLoopCost]
  rw [hsum,haloCellPhases_volume hst band a b]
  dsimp only [band]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
