module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRepeatedBatchCost
public import IntegerMultBounds.NLogN.PhaseCellHaloVolume

/-! Aggregate the same-origin replica ledger over generated halo cells. The
numerical setup is shared across replicas; every per-cell source scan stays paid. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def rawRepeatedHaloInteriorCost (p l B s t u target rhsExp a b : ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  ((haloCellPhases s t band a b).map (fun phase =>
    rawRepeatedBatchCost p l B (haloLength s t band a b phase) s t u target rhsExp
      (haloStart s t band a phase))).sum

theorem rawRepeatedHaloInteriorCost_eq {s t : ℕ} [NeZero s] (hst : s < t)
    (p l B u target rhsExp a b : ℕ) :
    let band := PhaseCellBand.width p u
    rawRepeatedHaloInteriorCost p l (B+1) s t u target rhsExp a b =
      rawRepeatedHaloInteriorCost p l 1 s t u target rhsExp a b+
        (B*(haloInterior s t band a b).card)*rawRepeatedBatchCoordinateCost p l target rhsExp+
        (B*(haloCellPhases s t band a b).length)*rawRepeatedBatchCellCost p l s target rhsExp := by
  dsimp only
  let band := PhaseCellBand.width p u
  have hsum (phases : List ℕ) :
      (phases.map (fun phase => rawRepeatedBatchCost p l (B+1)
        (haloLength s t band a b phase) s t u target rhsExp (haloStart s t band a phase))).sum =
      (phases.map (fun phase => rawRepeatedBatchCost p l 1
        (haloLength s t band a b phase) s t u target rhsExp (haloStart s t band a phase))).sum+
        (B*(phases.map (haloLength s t band a b)).sum)*rawRepeatedBatchCoordinateCost p l target rhsExp+
        (B*phases.length)*rawRepeatedBatchCellCost p l s target rhsExp := by
    induction phases with
    | nil => simp
    | cons phase phases ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      rw [rawRepeatedBatchCost_eq,ih]
      ring
  unfold rawRepeatedHaloInteriorCost
  rw [hsum,haloCellPhases_volume hst band a b]

theorem rawRepeatedHaloInteriorCost_le_volume {s t : ℕ} [NeZero s] (hst : s < t)
    (p l B u target rhsExp a b : ℕ) (hB : 0 < B) :
    let band := PhaseCellBand.width p u
    let w := executionWidth p l target rhsExp
    rawRepeatedHaloInteriorCost p l B s t u target rhsExp a b ≤
      ((haloCellPhases s t band a b).map (fun phase => repeatedClosedBatchCost p l 0
        (haloLength s t band a b phase) s t u target rhsExp (haloStart s t band a phase))).sum+
        (B*(haloInterior s t band a b).card)*repeatedBatchCoordinateCost p l target rhsExp+
        (B*(haloCellPhases s t band a b).length)*repeatedBatchCellCost p l target rhsExp+
        (haloCellPhases s t band a b).length*(250*(B*s*w)) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let w := executionWidth p l target rhsExp
  let setup := fun phase => repeatedClosedBatchCost p l 0 (haloLength s t band a b phase)
    s t u target rhsExp (haloStart s t band a phase)
  have hsum (phases : List ℕ) :
      (phases.map (fun phase => setup phase+
        (B*haloLength s t band a b phase)*repeatedBatchCoordinateCost p l target rhsExp+
        B*repeatedBatchCellCost p l target rhsExp+250*(B*s*w))).sum =
      (phases.map setup).sum+(B*(phases.map (haloLength s t band a b)).sum)*repeatedBatchCoordinateCost p l target rhsExp+
        (B*phases.length)*repeatedBatchCellCost p l target rhsExp+phases.length*(250*(B*s*w)) := by
    induction phases with
    | nil => simp
    | cons phase phases ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; ring
  have hh := List.sum_le_sum (l := haloCellPhases s t band a b) (fun phase hp => by
    have hL := ((mem_haloCellPhases s t band a b phase).mp hp).2
    have hstop := haloStop_le s t band b phase
    have hfit : haloStart s t band a phase+haloLength s t band a b phase ≤ s := by
      dsimp only [haloLength] at hL ⊢
      omega
    exact rawRepeatedBatchCost_le_volume p l B (haloLength s t band a b phase) s t u target rhsExp
      (haloStart s t band a phase) hB hL hfit)
  rw [hsum,haloCellPhases_volume hst band a b] at hh
  exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
