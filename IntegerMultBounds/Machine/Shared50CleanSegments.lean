import IntegerMultBounds.Machine.Shared50InitializedSegments
import IntegerMultBounds.Machine.FlatCoordinateCleanSchedule

/-! Actual nonrecursive Shared50 segments with physically restored workspace.
The exact field-program run is realized on the common payload, b/W headers are
preserved, and every other input and output tape is blank at head zero.
Recursive interchange execution remains a separate obligation. -/
namespace IntegerMultBounds.Machine.Shared50CleanSegments
open Networks
open Shared50ModularSchedule (Index)
open Shared50AffineControl (rationalSchedules)
open AffineFieldCoordinates
open Shared50NonrecursiveSegments (description)
open ActualAffineScaling (modulus)
noncomputable section

/-- One fixed clean machine implements an actual field segment at every width.
Its complete output bank is directly reusable as the next call's input: no
private metadata, generated dimensions, tracking marks or displaced heads remain. -/
theorem realizes (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (ops : List (AffineFieldProgram.Op Index ℚ)) (hs : ∀ op ∈ ops, op ∈ p)
    (hn : ∀ op ∈ ops, Nonrecursive op) (b W : ℕ) (hW : 0 < W)
    (a : FlatCoordinateStages.Array (125000+125000) b W) :
    let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    let stages := description p hp ops hs hn
    HoareTime (FlatCoordinateCleanSchedule.program stages)
      (fun v => v = SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common a)
        (FlatCoordinateCleanSchedule.tapeCount stages))
      (fun v => v = SharedBankStageInput.raw
        (FlatCoordinateShiftSharedBank.common (FlatCoordinateInitializedSchedule.array stages b W hW a))
        (FlatCoordinateCleanSchedule.tapeCount stages) ∧
        ∀ (s : Swap.Shear.State Index (ZMod (modulus b))) (j : Fin W),
          FlatCoordinateInitializedSchedule.array stages b W hW a
            (FlatCoordinateLayout.index (embed (AffineFieldProgram.run
              (ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))) s)) j) =
                a (FlatCoordinateLayout.index (embed s) j))
      (FlatCoordinateCleanSchedule.constant stages*((modulus b)^(125000+125000)*W)) := by
  dsimp only
  apply (FlatCoordinateCleanSchedule.realizes (description p hp ops hs hn) b W hW a).consequence
    (fun _ h => h) ?_ le_rfl
  intro v hv
  exact ⟨hv.1,Shared50InitializedSegments.array_entry p hp ops hs hn b W hW a⟩

end
end IntegerMultBounds.Machine.Shared50CleanSegments
