import IntegerMultBounds.Machine.Shared50OrderedPieces

/-! Expand the fixed actual interleaved control into certified nonrecursive
runs, explicit role-specific recursive boundaries, and certified scalar gates.
All source field operations survive in order. This is a finite controller input;
physical recursive-call assembly remains a separate obligation. -/
namespace IntegerMultBounds.Machine.Shared50PieceSchedule
noncomputable section
open Networks Shared50OrderedControl Shared50OrderedPieces
open Shared50GlobalBudget (World)
open Shared50ModularSchedule (Index)
open Shared50FixedControl (control)
open AffineFieldSegments
attribute [local irreducible] Shared50FixedControl.control Shared50GlobalCircuit.program50
  Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code

inductive Piece where
  | segment (seg : Segment)
  | call (wire : World) (i j : Index)
  | gate (gate : Gate)

/-- A boundary has the same wire as both neighboring runs. Empty runs are
retained, so even adjacent recursive calls have an explicit continuation slot. -/
def edgePieces (wire : World) (parent : FieldProgram)
    (hp : FramedControlSchedule.Step.edge wire parent ∈ control) :
    (s : Segments 125000 ℚ) →
    (∀ ops ∈ runs s, ops ∈ runs (split parent)) → List Piece
  | .done ops, hs => [.segment ⟨wire,parent,ops,hp,hs ops (by simp [runs])⟩]
  | .boundary ops i j tail, hs =>
      .segment ⟨wire,parent,ops,hp,hs ops (by simp [runs])⟩ :: .call wire i j ::
        edgePieces wire parent hp tail (fun ops h => hs ops (by simp only [runs,List.mem_cons]; exact Or.inr h))

def piecesOf (step : {step : Control // step ∈ control}) : List Piece :=
  match step with
  | ⟨.edge wire parent,hp⟩ => edgePieces wire parent hp (split parent) (fun _ h => h)
  | ⟨.gate g,hg⟩ => [.gate ⟨g,hg⟩]

/-- One fixed finite list, independent of every runtime width and dimension. -/
def pieces : List Piece := control.attach.flatMap piecesOf

inductive Atom where
  | field (wire : World) (op : AffineFieldProgram.Op Index ℚ)
  | gate (g : Circuit.Gate World (ZMod 2))

def expandPiece : Piece → List Atom
  | .segment seg => seg.ops.map (Atom.field seg.wire)
  | .call wire i j => [.field wire (.interchange i j)]
  | .gate gate => [.gate gate.scalar]

def expandControl : Control → List Atom
  | .edge wire p => p.map (Atom.field wire)
  | .gate g => [.gate g]

/-- Segmentation preserves every field instruction and its original wire. -/
theorem edgePieces_expand (wire : World) (parent : FieldProgram)
    (hp : FramedControlSchedule.Step.edge wire parent ∈ control)
    (s : Segments 125000 ℚ) (hs : ∀ ops ∈ runs s, ops ∈ runs (split parent)) :
    (edgePieces wire parent hp s hs).flatMap expandPiece =
      (flatten s).map (Atom.field wire) := by
  induction s with
  | done ops => simp only [edgePieces,List.flatMap_cons,List.flatMap_nil,List.append_nil,expandPiece,flatten]
  | boundary ops i j tail ih =>
    simp only [edgePieces,List.flatMap_cons,expandPiece,List.singleton_append,ih,
      flatten,List.map_append,List.map_cons]

theorem piecesOf_expand (step : {step : Control // step ∈ control}) :
    (piecesOf step).flatMap expandPiece = expandControl step.val := by
  obtain ⟨step,h⟩ := step
  cases step with
  | edge wire p => exact (edgePieces_expand wire p h (split p) _).trans (by rw [flatten_split]; rfl)
  | gate g => rfl

/-- Every field operation and scalar gate occurs at exactly its original place. -/
theorem expansion_exact : pieces.flatMap expandPiece = control.flatMap expandControl := by
  rw [pieces,List.flatMap_assoc]
  have he : (fun step : {step : Control // step ∈ control} => (piecesOf step).flatMap expandPiece) =
      fun step => expandControl step.val := funext piecesOf_expand
  rw [he]
  simp only [List.flatMap_def,List.attach_map_val]

def calls : Piece → ℕ
  | .call _ _ _ => 1
  | _ => 0

theorem edgePieces_calls (wire : World) (parent : FieldProgram)
    (hp : FramedControlSchedule.Step.edge wire parent ∈ control)
    (s : Segments 125000 ℚ) (hs : ∀ ops ∈ runs s, ops ∈ runs (split parent)) :
    ((edgePieces wire parent hp s hs).map calls).sum = recursiveCalls s := by
  induction s with
  | done ops => rfl
  | boundary ops i j tail ih =>
    simp only [edgePieces,List.map_cons,List.sum_cons,calls,zero_add,ih,recursiveCalls]
    omega

def controlCalls : Control → ℕ
  | .edge _ p => recursiveCalls (split p)
  | .gate _ => 0

theorem piecesOf_calls (step : {step : Control // step ∈ control}) :
    ((piecesOf step).map calls).sum = controlCalls step.val := by
  obtain ⟨step,h⟩ := step
  cases step with
  | edge wire p => exact edgePieces_calls wire p h (split p) _
  | gate g => rfl

private theorem controlCalls_sum (steps : List Control) :
    (steps.map controlCalls).sum = Shared50OrderedControl.calls steps := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
    cases step with
    | edge wire p => exact congrArg (recursiveCalls (split p) + ·) ih
    | gate g => simpa only [List.map_cons,List.sum_cons,controlCalls,zero_add,
        Shared50OrderedControl.calls,FramedControlSchedule.programs,List.filterMap_cons] using ih

/-- Exact count of literal recursive call instructions in the fixed list. -/
theorem calls_exact : (pieces.map calls).sum = Shared50Parameters.s := by
  rw [pieces,List.map_flatMap,List.flatMap_def,List.sum_flatten,List.map_map]
  have he : (fun step : {step : Control // step ∈ control} => ((piecesOf step).map calls).sum) =
      fun step => controlCalls step.val := funext piecesOf_calls
  change (control.attach.map (fun step => ((piecesOf step).map calls).sum)).sum = _
  rw [he,List.attach_map_val,controlCalls_sum,Shared50FixedControl.calls_exact]

end
end IntegerMultBounds.Machine.Shared50PieceSchedule
