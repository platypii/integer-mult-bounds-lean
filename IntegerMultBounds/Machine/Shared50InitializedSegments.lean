import IntegerMultBounds.Machine.Shared50NonrecursiveSegments
import IntegerMultBounds.Machine.FlatCoordinateInitializedSchedule

/-! Actual nonrecursive Shared50 segments from sole b/W and payload. This bridge
uses fully initialized physical stages; recursive interchanges remain explicit
separate obligations. -/
namespace IntegerMultBounds.Machine.Shared50InitializedSegments
open Networks
open Shared50ModularSchedule (Index)
open Shared50AffineControl (rationalSchedules)
open Shared50ModularControl (prime)
open AffineFieldCoordinates
open Shared50NonrecursiveSegments (description description_actions)
open ActualAffineScaling (modulus)
noncomputable section

/-- Every record symbol follows the exact field-program run through the whole
segment, with no assumed intermediate payloads. -/
theorem array_entry (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (ops : List (AffineFieldProgram.Op Index ℚ)) (hs : ∀ op ∈ ops, op ∈ p)
    (hn : ∀ op ∈ ops, Nonrecursive op)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array (125000+125000) b W)
    (s : Swap.Shear.State Index (ZMod (modulus b))) (j : Fin W) :
    let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    FlatCoordinateInitializedSchedule.array (description p hp ops hs hn) b W hW a
      (FlatCoordinateLayout.index (embed (AffineFieldProgram.run
        (ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))) s)) j) =
      a (FlatCoordinateLayout.index (embed s) j) := by
  dsimp only
  have hm : ∀ op ∈ ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b))),
      Nonrecursive op := by
    intro op hop
    obtain ⟨src,hsrc,rfl⟩ := List.mem_map.mp hop
    have hh := hn src hsrc
    cases src <;> exact hh
  have hh := FlatCoordinateInitializedSchedule.array_entry (description p hp ops hs hn) b W hW a (embed s) j
  rw [description_actions,segment_run _ hm] at hh
  exact hh


/-- A fixed physical machine executes the actual nonrecursive field segment
from just the array and canonical b/W headers. All private input tapes are blank;
dimension construction, copies, execution and joins are included in the bound. -/
theorem realizes (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (ops : List (AffineFieldProgram.Op Index ℚ)) (hs : ∀ op ∈ ops, op ∈ p)
    (hn : ∀ op ∈ ops, Nonrecursive op) (b W : ℕ) (hW : 0 < W) :
    let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    let stages := description p hp ops hs hn
    ∃ output : FlatCoordinateStages.Array (125000+125000) b W →
        Tapes (FlatCoordinateInitializedSchedule.skeleton stages).tapes prime,
      ∀ a, HoareTime (FlatCoordinateInitializedSchedule.skeleton stages).program
        (fun v => v = SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common a)
          (FlatCoordinateInitializedSchedule.skeleton stages).tapes)
        (fun v => v = output a ∧
          SharedBank.payload v (FlatCoordinateInitializedSchedule.skeleton stages).slots =
            FlatCoordinateShiftSharedBank.common
              (FlatCoordinateInitializedSchedule.array stages b W hW a) ∧
          ∀ (s : Swap.Shear.State Index (ZMod (modulus b))) (j : Fin W),
            FlatCoordinateInitializedSchedule.array stages b W hW a
              (FlatCoordinateLayout.index (embed (AffineFieldProgram.run
                (ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))) s)) j) =
                a (FlatCoordinateLayout.index (embed s) j))
        (FlatCoordinateInitializedSchedule.constant stages*((modulus b)^(125000+125000)*W)) := by
  dsimp only
  obtain ⟨output,hh⟩ :=
    FlatCoordinateInitializedSchedule.realizes (description p hp ops hs hn) b W hW
  refine ⟨output,?_⟩
  intro a
  apply (hh a).consequence (fun _ h => h) ?_ le_rfl
  intro v hv
  exact ⟨hv.1,hv.2.1,array_entry p hp ops hs hn b W hW a⟩

end
end IntegerMultBounds.Machine.Shared50InitializedSegments
