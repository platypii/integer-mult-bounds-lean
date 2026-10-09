import IntegerMultBounds.Machine.Shared50RecursiveChildPermutation

/-! Binary World payloads and blank shared I/O are the invariant of recursive
piece boundaries. Dirty World workspaces may contain arbitrary bits. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveBinaryInvariant
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50GlobalBudget (World)
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50NodePieceTransport (worldSlot)
open Shared50NodeSegments (payloadCount io)
open RecursiveMixedSchedule (Data)
variable {b : ℕ} {v : Descriptor}
local instance : NeZero (prime^b) := ⟨ne_of_gt (pow_pos Shared50ModularControl.prime_prime.pos _)⟩

def Ready (data : Data payloadCount v) : Prop :=
  ∃ bits : World → Fin (volume prime v) → ZMod 2,
    data = Shared50NodeGates.encoded bits (fun _ => blank)

theorem of_encoded (bits : World → Fin (volume prime v) → ZMod 2) :
    Ready (Shared50NodeGates.encoded bits (fun _ => blank)) := ⟨bits,rfl⟩

theorem io_blank {data : Data payloadCount v} (hr : Ready data) :
    data io = fun _ => blank := by
  obtain ⟨bits,rfl⟩ := hr
  rfl

theorem cells {data : Data payloadCount v} (hr : Ready data) (w : World)
    (z : Fin (volume prime v)) :
    ∃ bit : ZMod 2, data (worldSlot w) z = SparseRoleCircuit.encode (a := 0) bit := by
  obtain ⟨bits,rfl⟩ := hr
  exact ⟨bits w z,Shared50NodePieceTransport.encoded_entry bits (fun _ => blank) w z⟩

/-- Reconstruct the full bit arrays from literal encoded cells. -/
theorem of_cells (data : Data payloadCount v)
    (hc : ∀ w z, ∃ bit : ZMod 2, data (worldSlot w) z = SparseRoleCircuit.encode (a := 0) bit)
    (hi : data io = fun _ => blank) : Ready data := by
  classical
  refine ⟨fun w z => Classical.choose (hc w z), ?_⟩
  funext k z
  induction k using Fin.addCases with
  | left k =>
    have he := Classical.choose_spec (hc (Shared50TapeGlobal.roleEquiv k) z)
    simpa only [worldSlot,Equiv.symm_apply_apply,Shared50NodeGates.encoded,
      Shared50NodeGates.extend,Fin.addCases_left,Shared50RecursiveGates.encoded] using he
  | right k =>
    fin_cases k
    exact congrFun hi z

/-- Exact fieldwise semantics produce binary output at every flat cell. -/
theorem step (hw : v.width=125000*b) (child : Shared50NodePieceTransport.Child v)
    (hc : Shared50NodePieceTransport.ChildSpec hw child) (p : Shared50PieceSchedule.Piece)
    (data : Data payloadCount v) (hr : Ready data) :
    Ready (Shared50NodePieceTransport.step hw child p data) := by
  obtain ⟨bits,rfl⟩ := hr
  apply of_cells
  · intro w z
    obtain ⟨x,rfl⟩ := RecursiveScalarIndex.surjective (v := v) hw z
    have he := Shared50NodePieceTransport.represents_step hw child hc p x
      (Shared50NodeGates.encoded bits (fun _ => blank)) (Shared50NodePieceTransport.fiber hw bits x)
      (Shared50NodePieceTransport.represents_encoded hw bits (fun _ => blank) x)
    refine ⟨Shared50PieceSemantics.piece b p (Shared50NodePieceTransport.fiber hw bits x) w (x.h,x.d), ?_⟩
    exact he w (x.h,x.d)
  · rw [Shared50NodePieceTransport.step_io hw child hc]
    rfl

theorem run (hw : v.width=125000*b) (child : Shared50NodePieceTransport.Child v)
    (hc : Shared50NodePieceTransport.ChildSpec hw child) (ps : List Shared50PieceSchedule.Piece)
    (data : Data payloadCount v) (hr : Ready data) :
    Ready (Shared50NodePieceTransport.run hw child ps data) := by
  induction ps generalizing data with
  | nil => exact hr
  | cons p ps ih => exact ih _ (step hw child hc p data hr)

theorem segment (seg : Shared50OrderedPieces.Segment) (hw : v.width=125000*b)
    (data : Data payloadCount v) (hr : Ready data) :
    Ready (Shared50NodeSegments.array seg hw data) :=
  step hw (Shared50RecursiveChildPermutation.child hw) (Shared50RecursiveChildPermutation.child_spec hw)
    (.segment seg) data hr

theorem gate (g : Shared50OrderedPieces.Gate) (data : Data payloadCount v) (hr : Ready data) :
    Ready (Shared50NodeGates.array g data) := by
  obtain ⟨bits,rfl⟩ := hr
  rw [Shared50NodeGates.array_encoded]
  exact ⟨_,rfl⟩

theorem child (hw : v.width=125000*b) (w : World) (i j : Fin 125000)
    (data : Data payloadCount v) (hr : Ready data) :
    Ready (Shared50RecursiveChildPermutation.child hw w i j data) := by
  obtain ⟨bits,rfl⟩ := hr
  rw [Shared50RecursiveChildPermutation.child_encoded]
  exact ⟨_,rfl⟩

end
end IntegerMultBounds.Machine.Shared50RecursiveBinaryInvariant
