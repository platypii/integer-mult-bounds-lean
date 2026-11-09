module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProcessHaloLengthKeyStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArithmeticWorkspaceBound
import Mathlib.Tactic.Ring

/-! Halo publication adds stream volume to the selected numerical batch reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem protectedControlledHaloClassWorkspace_le_volume
    (J R K p l B L s t u target rhsExp a b : ℕ) :
    let q := executionPrecision p l target rhsExp
    protectedControlledHaloClassWorkspace J R K p l B L s t u target rhsExp a b ≤
      sizedClosedBatchWorkspace J R K p l B L s t u target rhsExp+
      20000*(B+s+a+b+1)*(q+1) := by
  dsimp only
  unfold protectedControlledHaloClassWorkspace protectedBatchSolveWorkspace rawNaturalGatherCost
  simp only [executionWidth,executionPrecision]
  ring_nf
  omega

theorem processHaloLengthKeyWorkspace_le_components
    (J R K p l L s t u target rhsExp V a b : ℕ) :
    let q := executionPrecision p l target rhsExp
    let band := PhaseCellBand.width p u
    let B := (haloLengthGroup s t band a b L).length
    processHaloLengthKeyWorkspace J R K p l L s t u target rhsExp V a b ≤
      conditionalHaloGroupPreparationWorkspace (2^15*p) (executionStagePrecision p l target rhsExp+1)
        q l s t u band a b L+
      sizedClosedBatchWorkspace J R K p l B L s t u target rhsExp+
      20000*(B+s+a+b+1)*(q+1)+3*(6*L+19*V+14) := by
  dsimp only
  have h := protectedControlledHaloClassWorkspace_le_volume J R K p l
    (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length L s t u target rhsExp a b
  unfold processHaloLengthKeyWorkspace conditionalHaloClassWorkspace
  dsimp only
  split <;> omega

theorem sizedClosedBatchWorkspace_le_volume
    (J R K p l B L s t u target rhsExp : ℕ) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    sizedClosedBatchWorkspace J R K p l B L s t u target rhsExp ≤
      generatedBatchSetupWorkspace J (2^15*p) (j+1) q s t u (PhaseCellBand.width p u) l L 0+
      cellArithmeticWorkspace R K q (sourceExponent l target rhsExp) (8*p+1) l w B L+
      30000*(B+1)*(L+1)*(q+l+1) := by
  dsimp only
  unfold sizedClosedBatchWorkspace stagedCellWorkspace publishedCellWorkspace
  dsimp only
  rw [generatedBatchSetupWorkspace_affine]
  unfold stagePayloadCost fetchPageCost publishFromDimensionsCost releaseBatchRuntimeCost
    releaseRuntimePagesCost swapCellPayloadCost releaseGeneratorPageCost releaseWeightPageCost
  simp only [executionWidth,executionPrecision]
  ring_nf
  omega

private theorem add_bound_of_middle {x a b c d e : ℕ} (h : x ≤ a+b+c) (hb : b ≤ d+e) :
    x ≤ a+d+(e+c) := by omega

theorem sizedClosedBatchWorkspace_le_shared_setup
    (J R K p l B L s t u target rhsExp : ℕ) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    sizedClosedBatchWorkspace J R K p l B L s t u target rhsExp ≤
      generatedBatchSetupWorkspace J (2^15*p) (j+1) q s t u (PhaseCellBand.width p u) l L 0+
      cellArithmeticWorkspace R K q cExp (8*p+1) l w 0 L+
      (100000*(R+K+1)*B*(2^l+L+1)*(w+cExp+(8*p+1)+l+1)+
        30000*(B+1)*(L+1)*(q+l+1)) := by
  dsimp only
  have hb := sizedClosedBatchWorkspace_le_volume J R K p l B L s t u target rhsExp
  have ha := cellArithmeticWorkspace_le_affine R K (executionPrecision p l target rhsExp)
    (sourceExponent l target rhsExp) (8*p+1) l (executionWidth p l target rhsExp) B L
  dsimp only at hb
  exact add_bound_of_middle hb ha

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
