module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySeamSequence

/-! Charge control generation separately from the linear publication volume.
The same bound covers every slot, so the loop shares its workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellMatrix

def boundarySeamBudget (N D s W : ℕ) : ℕ :=
  16*TableVM.tblC D 0+106*D+425*(N+1)*(s*W)

theorem boundarySlotMasterPreparationCost_le (slot : Fin 3) (N w D s width W : ℕ)
    (hs : 1 ≤ s) (hW : 1 ≤ W) (hw : w ≤ W) (hwidth : width ≤ s) :
    boundarySlotMasterPreparationCost slot N w D s width W ≤
      16*TableVM.tblC D 0+106*D+160*(N+1)*(s*W) := by
  have hvol : 1 ≤ s*W := Nat.mul_pos hs hW
  have hsmall : s ≤ s*W := by nlinarith
  have hwidthW := Nat.mul_le_mul_right W hwidth
  have hwidthw : width*w ≤ s*W := (Nat.mul_le_mul_left width hw).trans hwidthW
  have hN : N ≤ N*(s*W) := by nlinarith
  have hNwidth := Nat.mul_le_mul_left N hwidthw
  unfold boundarySlotMasterPreparationCost
  split
  · unfold firstBoundaryMasterPreparationCost
    nlinarith
  · have hL : coreLength s width (boundaryCropIndex s width slot) ≤ s := by
      unfold coreLength
      omega
    have hLW := Nat.mul_le_mul_right W hL
    have hLw : coreLength s width (boundaryCropIndex s width slot)*w ≤ s*W :=
      (Nat.mul_le_mul_left _ hw).trans hLW
    have hNLw := Nat.mul_le_mul_left N hLw
    dsimp only
    nlinarith

theorem preparedStandardSeamCost_le (preparationCost N w s width k W : ℕ)
    (hs : 1 ≤ s) (hW : 1 ≤ W) (hw : w ≤ W) (hstart : coreStart width k ≤ s) :
    preparedStandardSeamCost preparationCost N w s width k W ≤
      preparationCost+265*(N+1)*(s*W) := by
  have hL : coreLength s width k ≤ s := by unfold coreLength; omega
  have hpub := restoringSeamCost_le w W N s (coreStart width k) (coreLength s width k)
    hs hW hw hstart hL
  have haW := Nat.mul_le_mul_right W hstart
  have hLW := Nat.mul_le_mul_right W hL
  have hLw : coreLength s width k*w ≤ s*W := (Nat.mul_le_mul_left _ hw).trans hLW
  have hNLw := Nat.mul_le_mul_left N hLw
  have hvol : 1 ≤ s*W := Nat.mul_pos hs hW
  unfold preparedStandardSeamCost
  nlinarith

theorem boundarySlotSeamCost_le (slot : Fin 3) (N w D s width W : ℕ)
    (hs : 1 ≤ s) (hW : 1 ≤ W) (hw : w ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) :
    boundarySlotSeamCost slot N w D s width W ≤
      16*TableVM.tblC D 0+106*D+425*(N+1)*(s*W) := by
  have hmem : boundaryCropIndex s width slot ∈ boundaryCropSchedule s width := by
    fin_cases slot <;> simp [boundaryCropIndex,boundaryCropSchedule]
  have hstart := ((boundaryCropSchedule_spec s width hwidth hroom).2.2 _ hmem).2.1.le
  have hprep := boundarySlotMasterPreparationCost_le slot N w D s width W hs hW hw (by omega)
  have hpub := preparedStandardSeamCost_le
    (boundarySlotMasterPreparationCost slot N w D s width W) N w s width
    (boundaryCropIndex s width slot) W hs hW hw hstart
  unfold boundarySlotSeamCost
  nlinarith

theorem boundarySeamCost_le (N w D s width W : ℕ)
    (hs : 1 ≤ s) (hW : 1 ≤ W) (hw : w ≤ W)
    (hwidth : 0 < width) (hroom : 3*width < s) :
    boundarySeamCost N w D s width W ≤
      16*TableVM.tblC D 0+106*D+425*(N+1)*(s*W) := by
  unfold boundarySeamCost
  exact max_le (boundarySlotSeamCost_le 0 N w D s width W hs hW hw hwidth hroom)
    (max_le (boundarySlotSeamCost_le 1 N w D s width W hs hW hw hwidth hroom)
      (boundarySlotSeamCost_le 2 N w D s width W hs hW hw hwidth hroom))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
