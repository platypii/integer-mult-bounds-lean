import IntegerMultBounds.Machine.Shared50NonrecursiveCoordinates

/-! Fixed nonrecursive segments of actual Shared50 schedules execute on one
uniform physical machine. Canonical dimension descriptors are supplied here;
recursive interchange operations remain excluded explicitly. -/
namespace IntegerMultBounds.Machine.Shared50NonrecursiveSegments
open Networks
open Shared50ModularSchedule (Index)
open Shared50AffineControl (rationalSchedules)
open Shared50ModularControl (prime)
open FlatCoordinateSchedule AffineFieldCoordinates
open ActualAffineScaling (modulus)
noncomputable section

def description (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (ops : List (AffineFieldProgram.Op Index ℚ)) (hs : ∀ op ∈ ops, op ∈ p)
    (hn : ∀ op ∈ ops, Nonrecursive op) : List (FlatCoordinateSchedule.Op (125000+125000)) :=
  ofList (ops.flatMap expand) (by
    intro out hout
    obtain ⟨op,hop,he⟩ := List.mem_flatMap.mp hout
    exact Shared50NonrecursiveCoordinates.expanded_supported p hp op (hs op hop) (hn op hop) out he)

theorem description_rational (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (ops : List (AffineFieldProgram.Op Index ℚ)) (hs : ∀ op ∈ ops, op ∈ p)
    (hn : ∀ op ∈ ops, Nonrecursive op) :
    (description p hp ops hs hn).map FlatCoordinateSchedule.Op.rational = ops.flatMap expand :=
  rational_ofList _ _

theorem description_actions (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (ops : List (AffineFieldProgram.Op Index ℚ)) (hs : ∀ op ∈ ops, op ∈ p)
    (hn : ∀ op ∈ ops, Nonrecursive op) (b : ℕ) :
    (description p hp ops hs hn).map (fun op => op.action b) =
      (ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))).flatMap expand := by
  change (description p hp ops hs hn).map
    ((OrderedAffine.mapOp (Swap.Modular.ratMod (modulus b))) ∘ FlatCoordinateSchedule.Op.rational) = _
  rw [← List.map_map,description_rational,List.map_flatMap,List.flatMap_map]
  congr 1
  funext op
  exact expand_map _ (Swap.Modular.ratMod_one _) (by simp [Swap.Modular.ratMod]) op

/-- Every record symbol follows the exact field-program run through the whole
segment, with no assumed intermediate payloads. -/
theorem array_entry (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (ops : List (AffineFieldProgram.Op Index ℚ)) (hs : ∀ op ∈ ops, op ∈ p)
    (hn : ∀ op ∈ ops, Nonrecursive op)
    (b W : ℕ) (hW : 0 < W) (a : FlatCoordinateStages.Array (125000+125000) b W)
    (s : Swap.Shear.State Index (ZMod (modulus b))) (j : Fin W) :
    let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    FlatCoordinateScheduleCompile.array (description p hp ops hs hn) b W hW a
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
  have hh := FlatCoordinateScheduleCompile.array_entry (description p hp ops hs hn) b W hW a (embed s) j
  rw [description_actions,segment_run _ hm] at hh
  exact hh

/-- The machine and linear constant depend only on the fixed rational segment,
not on the runtime width, record size, or input symbols. Its metadata bank is
independent of the payload; dimensions are still canonical supplied inputs. -/
theorem realizes (p : List (AffineFieldProgram.Op Index ℚ)) (hp : p ∈ rationalSchedules)
    (ops : List (AffineFieldProgram.Op Index ℚ)) (hs : ∀ op ∈ ops, op ∈ p)
    (hn : ∀ op ∈ ops, Nonrecursive op) (b W : ℕ) (hW : 0 < W) :
    let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    let stages := description p hp ops hs hn
    ∃ (input output : FlatCoordinateStages.Array (125000+125000) b W →
        Tapes (FlatCoordinateScheduleCompile.skeleton stages).tapes prime)
      (metadata : Tapes (FlatCoordinateScheduleCompile.skeleton stages).tapes prime),
      (∀ a, SharedPayload.payload (input a) (FlatCoordinateScheduleCompile.skeleton stages).source
        (FlatCoordinateScheduleCompile.skeleton stages).dest = FlatAffineScalingPayload.pair a) ∧
      (∀ a, SharedPayload.strip (input a) (FlatCoordinateScheduleCompile.skeleton stages).source
        (FlatCoordinateScheduleCompile.skeleton stages).dest = metadata) ∧
      (∀ a, HoareTime (FlatCoordinateScheduleCompile.skeleton stages).program (fun v => v = input a)
        (fun v => v = output a ∧
          SharedPayload.payload v (FlatCoordinateScheduleCompile.skeleton stages).source
            (FlatCoordinateScheduleCompile.skeleton stages).dest =
              FlatAffineScalingPayload.pair (FlatCoordinateScheduleCompile.array stages b W hW a) ∧
          ∀ (s : Swap.Shear.State Index (ZMod (modulus b))) (j : Fin W),
            FlatCoordinateScheduleCompile.array stages b W hW a
              (FlatCoordinateLayout.index (embed (AffineFieldProgram.run
                (ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))) s)) j) =
                a (FlatCoordinateLayout.index (embed s) j))
        (FlatCoordinateScheduleCompile.constant stages*((modulus b)^(125000+125000)*W))) := by
  dsimp only
  obtain ⟨input,output,metadata,hi,hm,hh⟩ :=
    FlatCoordinateScheduleCompile.realizes (description p hp ops hs hn) b W hW
  refine ⟨input,output,metadata,hi,hm,?_⟩
  intro a
  apply (hh a).consequence (fun _ h => h) ?_ le_rfl
  intro v hv
  exact ⟨hv.1,hv.2.1,array_entry p hp ops hs hn b W hW a⟩

end
end IntegerMultBounds.Machine.Shared50NonrecursiveSegments
