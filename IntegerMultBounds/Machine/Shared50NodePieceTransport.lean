import IntegerMultBounds.Machine.Shared50NodeGates
import IntegerMultBounds.Machine.Shared50PieceSemantics

/-! Fiberwise correctness of the actual node payload transformations, in the
literal Shared50 piece order. Recursive calls expose only their exact original
field-interchange contract; segment and gate actions are the physical arrays. -/
namespace IntegerMultBounds.Machine.Shared50NodePieceTransport
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50GlobalBudget (World)
open Shared50TapeGlobal (roleCount roleEquiv)
open Shared50NodeSegments (payloadCount io)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveScalarCoordinates (Address index)
open RecursiveMixedSchedule (Data)
open Shared50OrderedControl (specializes edgeAction)
open Shared50ModularExecution (Arrays)
open Shared50PieceSchedule (Piece)
variable {b : ℕ} {v : Descriptor}
local instance : NeZero (prime^b) := ⟨ne_of_gt (pow_pos Shared50ModularControl.prime_prime.pos _)⟩
attribute [local irreducible] Shared50FixedControl.control Shared50GlobalCircuit.program50
  Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code
  Shared50AffineControl.rationalSchedules Shared50AffineControl.schedules

def worldSlot (w : World) : Fin payloadCount := Fin.castAdd 1 (roleEquiv.symm w)

theorem worldSlot_injective : Function.Injective worldSlot :=
  (Fin.castAdd_injective roleCount 1).comp roleEquiv.symm.injective

def withState (x : Address 125000 b v) (s : Shared50ModularExecution.Address (prime^b)) : Address 125000 b v :=
  {x with h := s.1, d := s.2}

def Represents (hw : v.width=125000*b) (x : Address 125000 b v)
    (data : Data payloadCount v) (stored : World → Arrays (prime^b)) : Prop :=
  ∀ w s, data (worldSlot w) (index hw (withState x s)) = SparseRoleCircuit.encode (a := 0) (stored w s)

def fiber (hw : v.width=125000*b) (bits : World → Fin (volume prime v) → ZMod 2)
    (x : Address 125000 b v) : World → Arrays (prime^b) :=
  fun w s => bits w (index hw (withState x s))

theorem encoded_entry (bits : World → Fin (volume prime v) → ZMod 2)
    (extra : Fin (volume prime v) → Fin 4) (w : World) (z : Fin (volume prime v)) :
    Shared50NodeGates.encoded bits extra (worldSlot w) z = SparseRoleCircuit.encode (a := 0) (bits w z) := by
  simp only [Shared50NodeGates.encoded,Shared50NodeGates.extend,worldSlot,Fin.addCases_left,
    Shared50RecursiveGates.encoded,Equiv.apply_symm_apply]

theorem represents_encoded (hw : v.width=125000*b) (bits : World → Fin (volume prime v) → ZMod 2)
    (extra : Fin (volume prime v) → Fin 4) (x : Address 125000 b v) :
    Represents hw x (Shared50NodeGates.encoded bits extra) (fiber hw bits x) :=
  fun w _s => encoded_entry bits extra w _

/-- A forward permutation contract determines the existing inverse edge action. -/
theorem represents_edge (hw : v.width=125000*b) (x : Address 125000 b v)
    (data out : Data payloadCount v) (stored : World → Arrays (prime^b))
    (hr : Represents hw x data stored) (w : World) (p : Shared50OrderedControl.FieldProgram)
    (hp : Shared50PieceSemantics.Legal b p)
    (he : ∀ s, out (worldSlot w) (index hw (withState x (AffineFieldProgram.run (specializes b p) s))) =
      data (worldSlot w) (index hw (withState x s)))
    (ho : ∀ k, k ≠ w → out (worldSlot k) = data (worldSlot k)) :
    Represents hw x out (Function.update stored w (edgeAction b p (stored w))) := by
  intro k s
  by_cases hk : k = w
  · subst k
    obtain ⟨y,rfl⟩ := (Shared50PieceSemantics.bijective b p hp).2 s
    rw [he,hr,Function.update_self,Shared50PieceSemantics.edge_entry b p hp]
  · rw [ho k hk,hr,Function.update_of_ne hk]

theorem represents_segment (seg : Shared50OrderedPieces.Segment) (hw : v.width=125000*b)
    (x : Address 125000 b v) (data : Data payloadCount v) (stored : World → Arrays (prime^b))
    (hr : Represents hw x data stored) :
    Represents hw x (Shared50NodeSegments.array seg hw data) (Shared50PieceSemantics.piece b (.segment seg) stored) := by
  apply represents_edge hw x data _ stored hr seg.wire seg.ops
  · exact Shared50PieceSemantics.legal_sublist b seg.parent seg.ops
      (Shared50PieceSemantics.legal_actual b seg.parent (Shared50OrderedPieces.segment_spec seg).1)
      (Shared50OrderedPieces.segment_spec seg).2.1
  · intro s
    exact Shared50NodeSegments.array_entry seg hw data (withState x s)
  · intro k hk
    exact Shared50NodeSegments.array_other seg hw data (worldSlot k) (worldSlot_injective.ne hk)

/-- A gate reads only original World roles at the same symbol position. -/
theorem gate_congr (g : Shared50OrderedPieces.Gate) (data other : Data payloadCount v)
    (z : Fin (volume prime v)) (h : ∀ k : Fin roleCount, data (Fin.castAdd 1 k) z = other (Fin.castAdd 1 k) z)
    (k : Fin roleCount) :
    Shared50NodeGates.array g data (Fin.castAdd 1 k) z = Shared50NodeGates.array g other (Fin.castAdd 1 k) z := by
  by_cases hk : k = (Shared50RecursiveGates.physical g).dst
  · subst k
    simp only [Shared50NodeGates.array,Shared50NodeGates.ops,RecursiveMixedSchedule.run,List.foldl_cons,
      List.foldl_nil,RecursiveMixedSchedule.transform,Shared50NodeGates.physical,Function.update_self]
    rw [h,h]
  · have hn := (Fin.castAdd_injective roleCount 1).ne hk
    simp only [Shared50NodeGates.array,Shared50NodeGates.ops,RecursiveMixedSchedule.run,List.foldl_cons,
      List.foldl_nil,RecursiveMixedSchedule.transform,Shared50NodeGates.physical,Function.update_of_ne hn]
    exact h k

theorem represents_gate (g : Shared50OrderedPieces.Gate) (hw : v.width=125000*b)
    (x : Address 125000 b v) (data : Data payloadCount v) (stored : World → Arrays (prime^b))
    (hr : Represents hw x data stored) :
    Represents hw x (Shared50NodeGates.array g data) (Shared50PieceSemantics.piece b (.gate g) stored) := by
  intro w s
  let ref := Shared50NodeGates.encoded (v := v) (fun w _ => stored w s) (fun _ => 0)
  have hc := gate_congr g data ref (index hw (withState x s)) (fun k => by
    have hh := hr (roleEquiv k) s
    simpa only [worldSlot,Equiv.symm_apply_apply,ref,Shared50NodeGates.encoded,Shared50NodeGates.extend,
      Fin.addCases_left,Shared50RecursiveGates.encoded] using hh) (roleEquiv.symm w)
  change Shared50NodeGates.array g data (worldSlot w) _ = _ at hc
  rw [hc]
  change Shared50NodeGates.array g (Shared50NodeGates.encoded _ _) (worldSlot w) _ = _
  rw [Shared50NodeGates.array_encoded,encoded_entry]
  simp only [Shared50PieceSemantics.piece,FramedCircuit.moduleGate_pointwise]

abbrev Child (v : Descriptor) := World → Shared50ModularSchedule.Index → Shared50ModularSchedule.Index →
  Data payloadCount v → Data payloadCount v

/-- A recursive call exchanges precisely its chosen H/D coordinates and keeps
all other payload roles, including the separate I/O role, intact. -/
structure ChildSpec (hw : v.width=125000*b) (child : Child v) : Prop where
  entry : ∀ w i j data (x : Address 125000 b v),
    child w i j data (worldSlot w)
      (index hw (withState x (AffineFieldProgram.execute (.interchange i j) (x.h,x.d)))) =
      data (worldSlot w) (index hw x)
  other : ∀ w i j data k, k ≠ worldSlot w → child w i j data k = data k

def step (hw : v.width=125000*b) (child : Child v) (p : Piece) (data : Data payloadCount v) : Data payloadCount v :=
  match p with
  | .segment seg => Shared50NodeSegments.array seg hw data
  | .gate g => Shared50NodeGates.array g data
  | .call w i j => child w i j data

def run (hw : v.width=125000*b) (child : Child v) (ps : List Piece) (data : Data payloadCount v) :=
  ps.foldl (fun data p => step hw child p data) data


theorem represents_call (hw : v.width=125000*b) (child : Child v) (hc : ChildSpec hw child)
    (w : World) (i j : Shared50ModularSchedule.Index) (x : Address 125000 b v)
    (data : Data payloadCount v) (stored : World → Arrays (prime^b)) (hr : Represents hw x data stored) :
    Represents hw x (child w i j data) (Shared50PieceSemantics.piece b (.call w i j) stored) := by
  apply represents_edge hw x data _ stored hr w [.interchange i j]
  · intro op hop
    simp only [specializes,List.map_cons,List.map_nil,List.mem_singleton,AffineFieldProgram.mapOp] at hop
    subst op
    trivial
  · intro s
    exact hc.entry w i j data (withState x s)
  · intro k hk
    exact hc.other w i j data (worldSlot k) (worldSlot_injective.ne hk)

theorem represents_step (hw : v.width=125000*b) (child : Child v) (hc : ChildSpec hw child)
    (p : Piece) (x : Address 125000 b v) (data : Data payloadCount v)
    (stored : World → Arrays (prime^b)) (hr : Represents hw x data stored) :
    Represents hw x (step hw child p data) (Shared50PieceSemantics.piece b p stored) := by
  cases p with
  | segment seg => exact represents_segment seg hw x data stored hr
  | gate g => exact represents_gate g hw x data stored hr
  | call w i j => exact represents_call hw child hc w i j x data stored hr

theorem represents_run (hw : v.width=125000*b) (child : Child v) (hc : ChildSpec hw child)
    (ps : List Piece) (x : Address 125000 b v) (data : Data payloadCount v)
    (stored : World → Arrays (prime^b)) (hr : Represents hw x data stored) :
    Represents hw x (run hw child ps data) (Shared50PieceSemantics.run b ps stored) := by
  induction ps generalizing data stored with
  | nil => exact hr
  | cons p ps ih => exact ih _ _ (represents_step hw child hc p x data stored hr)

theorem io_ne_worldSlot (w : World) : io ≠ worldSlot w := by
  intro he
  have hv := congrArg Fin.val he
  have hk := (roleEquiv.symm w).isLt
  simp only [io,worldSlot,Fin.val_last,Fin.val_castAdd] at hv
  omega

theorem step_io (hw : v.width=125000*b) (child : Child v) (hc : ChildSpec hw child)
    (p : Piece) (data : Data payloadCount v) : step hw child p data io = data io := by
  cases p with
  | segment seg => exact Shared50NodeSegments.array_io seg hw data
  | gate g => exact Shared50NodeGates.array_io g data
  | call w i j => exact hc.other w i j data io (io_ne_worldSlot w)

theorem run_io (hw : v.width=125000*b) (child : Child v) (hc : ChildSpec hw child)
    (ps : List Piece) (data : Data payloadCount v) : run hw child ps data io = data io := by
  induction ps generalizing data with
  | nil => rfl
  | cons p ps ih => exact (ih _).trans (step_io hw child hc p data)

/-- The literal physical-array list has exactly the original routed transpose
semantics at every original scalar coordinate, conditional only on each child
call's precise interchange semantics. -/
theorem run_entry (hw : v.width=125000*b) (child : Child v) (hc : ChildSpec hw child)
    (bits : World → Fin (volume prime v) → ZMod 2) (extra : Fin (volume prime v) → Fin 4)
    (w : World) (x : Address 125000 b v) :
    run hw child Shared50PieceSchedule.pieces (Shared50NodeGates.encoded bits extra)
      (worldSlot w) (index hw x) =
      SparseRoleCircuit.encode (a := 0) (bits (Shared50ShearEndpoints.route w)
        (index hw {x with h := x.d, d := x.h})) := by
  have hh := represents_run hw child hc Shared50PieceSchedule.pieces x
    (Shared50NodeGates.encoded bits extra) (fiber hw bits x) (represents_encoded hw bits extra x)
  rw [Shared50PieceSemantics.run_identity] at hh
  exact hh w (x.h,x.d)

end
end IntegerMultBounds.Machine.Shared50NodePieceTransport
