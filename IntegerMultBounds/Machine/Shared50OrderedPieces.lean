import IntegerMultBounds.Networks.Shared50FixedControl
import IntegerMultBounds.Machine.Shared50CleanSegments
import IntegerMultBounds.Machine.Shared50TapeGlobal

/-! Fixed physical implementations of pieces of the actual interleaved Shared50
control. Segment certificates retain their original role and parent schedule;
scalar gates use the same fixed global role enumeration as the tape circuit.
This does not supply recursive interchange continuations or a whole-bank join. -/
namespace IntegerMultBounds.Machine.Shared50OrderedPieces
noncomputable section
open Networks Shared50OrderedControl
open Shared50GlobalBudget (World)
open Shared50FixedControl (control)
open ActualAffineScaling (modulus)
attribute [local irreducible] Shared50FixedControl.control Shared50GlobalCircuit.program50
  Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code

/-- An actual maximal nonrecursive run, with its original physical wire. -/
structure Segment where
  wire : World
  parent : FieldProgram
  ops : FieldProgram
  member : FramedControlSchedule.Step.edge wire parent ∈ control
  run_member : ops ∈ AffineFieldSegments.runs (AffineFieldSegments.split parent)

theorem segment_spec (seg : Segment) :
    seg.parent ∈ Shared50AffineControl.rationalSchedules ∧
    (∀ op ∈ seg.ops, op ∈ seg.parent) ∧
    (∀ op ∈ seg.ops, AffineFieldCoordinates.Nonrecursive op) := by
  have h : seg.parent ∈ FramedControlSchedule.programs control :=
    List.mem_filterMap.mpr ⟨.edge seg.wire seg.parent,seg.member,rfl⟩
  rw [Shared50FixedControl.programs_exact] at h
  exact ⟨h,AffineFieldSegments.split_run_spec _ _ seg.run_member⟩

def stages (seg : Segment) := Shared50NonrecursiveSegments.description seg.parent
  (segment_spec seg).1 seg.ops (segment_spec seg).2.1 (segment_spec seg).2.2

def segmentProgram (seg : Segment) := FlatCoordinateCleanSchedule.program (stages seg)

/-- Every certified nonrecursive piece has one fixed clean physical machine.
Both runtime headers and all private blank tapes are restored exactly. -/
theorem segment_realizes (seg : Segment) (b W : ℕ) (hW : 0 < W)
    (a : FlatCoordinateStages.Array (125000+125000) b W) :
    let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
    HoareTime (segmentProgram seg)
      (fun v => v = SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common a)
        (FlatCoordinateCleanSchedule.tapeCount (stages seg)))
      (fun v => v = SharedBankStageInput.raw
        (FlatCoordinateShiftSharedBank.common
          (FlatCoordinateInitializedSchedule.array (stages seg) b W hW a))
        (FlatCoordinateCleanSchedule.tapeCount (stages seg)) ∧
        ∀ (s : Swap.Shear.State Shared50ModularSchedule.Index (ZMod (modulus b))) (j : Fin W),
          FlatCoordinateInitializedSchedule.array (stages seg) b W hW a
            (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (AffineFieldProgram.run
              (seg.ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))) s)) j) =
                a (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j))
      (FlatCoordinateCleanSchedule.constant (stages seg)*((modulus b)^(125000+125000)*W)) :=
  Shared50CleanSegments.realizes seg.parent (segment_spec seg).1 seg.ops
    (segment_spec seg).2.1 (segment_spec seg).2.2 b W hW a

/-- An actual scalar instruction at its retained interleaved position. -/
structure Gate where
  scalar : Circuit.Gate World (ZMod 2)
  member : FramedControlSchedule.Step.gate scalar ∈ control

theorem gate_xor (gate : Gate) : OneSourceCircuit.IsXor [gate.scalar] := by
  have hg : gate.scalar ∈ FramedControlSchedule.gates control :=
    List.mem_filterMap.mpr ⟨.gate gate.scalar,gate.member,rfl⟩
  rw [Shared50FixedControl.gates_exact] at hg
  intro g h
  have he : g = gate.scalar := List.mem_singleton.mp h
  subst g
  exact Shared50XorLists.global50 gate.scalar hg

def gateProgram {a : ℕ} (gate : Gate) :=
  OneSourceCircuit.program (a := a) Shared50TapeGlobal.roleEquiv [gate.scalar] (gate_xor gate)

/-- A scalar piece updates the exact original module gate on its named global
role tapes, preserving every other role, background cell, head, and counter. -/
theorem gate_realizes {a L : ℕ} (gate : Gate)
    (background : Fin Shared50TapeGlobal.roleCount → ℤ → Fin (a+4))
    (origins : Fin Shared50TapeGlobal.roleCount → ℤ)
    (data : World → Fin L → ZMod 2) (bs : List Bool) (hL : Counter.value bs = L) :
    HoareTime (gateProgram (a := a) gate)
      (fun v => v = PointwiseRoleGate.bank background origins
        (SparseRoleCircuit.encoded (fun k i => data (Shared50TapeGlobal.roleEquiv k) i)) bs)
      (fun v => v = PointwiseRoleGate.bank background origins
        (SparseRoleCircuit.encoded (fun k i =>
          FramedCircuit.moduleGate gate.scalar data (Shared50TapeGlobal.roleEquiv k) i)) bs)
      (14*L+14*bs.length+34) := by
  have h := OneSourceCircuit.circuit_hoare Shared50TapeGlobal.roleEquiv [gate.scalar]
    (gate_xor gate) background origins data bs hL
  simpa only [gateProgram,List.length_singleton,one_mul,Circuit.run_cons,Circuit.run_nil,
    ← FramedCircuit.moduleGate_pointwise] using h

end
end IntegerMultBounds.Machine.Shared50OrderedPieces
