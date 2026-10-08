import IntegerMultBounds.Machine.Shared50PieceSchedule
import IntegerMultBounds.Networks.AffineFieldBijective

/-! Exact semantic execution of the actual fixed piece list. Segment expansion,
literal recursive interchanges and pointwise gates retain their original order;
flattening back to fixed control yields its full routed-transpose identity. -/
namespace IntegerMultBounds.Machine.Shared50PieceSemantics
noncomputable section
open Networks
open Shared50GlobalBudget (World)
open Shared50ModularControl (prime)
open Shared50OrderedControl (FieldProgram Control specializes edgeAction)
open Shared50PieceSchedule (Piece Atom)
open Shared50ModularExecution (Arrays)
variable (b : ℕ)
local instance : NeZero (prime^b) := ⟨ne_of_gt (pow_pos Shared50ModularControl.prime_prime.pos _)⟩
attribute [local irreducible] Shared50FixedControl.control Shared50GlobalCircuit.program50
  Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code
  Shared50AffineControl.rationalSchedules Shared50AffineControl.schedules

/-- Actual modular legality, inherited from the protected rational schedules. -/
def Legal (p : FieldProgram) : Prop := ∀ op ∈ specializes b p, AffineFieldProgram.Legal op

theorem legal_actual (p : FieldProgram) (hp : p ∈ Shared50AffineControl.rationalSchedules) : Legal b p := by
  apply Shared50AffineControl.schedules_legal b
  rw [Shared50AffineControl.schedules_eq_map]
  exact List.mem_map.mpr ⟨p,hp,rfl⟩

theorem legal_sublist (p q : FieldProgram) (hp : Legal b p) (hq : ∀ op ∈ q, op ∈ p) : Legal b q := by
  intro op hop
  obtain ⟨src,hsrc,rfl⟩ := List.mem_map.mp hop
  exact hp _ (List.mem_map.mpr ⟨src,hq src hsrc,rfl⟩)

theorem legal_append (p q : FieldProgram) (hp : Legal b p) (hq : Legal b q) : Legal b (p++q) := by
  intro op hop
  simp only [specializes,List.map_append,List.mem_append] at hop
  exact hop.elim (hp op) (hq op)

theorem bijective (p : FieldProgram) (hp : Legal b p) :
    Function.Bijective (AffineFieldProgram.run (specializes b p)) :=
  AffineFieldBijective.run_bijective _ hp

/-- Exact forward-entry law for the existing inverse-function edge semantics. -/
theorem edge_entry (p : FieldProgram) (hp : Legal b p) (f : Arrays (prime^b))
    (x : Shared50ModularExecution.Address (prime^b)) :
    edgeAction b p f (AffineFieldProgram.run (specializes b p) x) = f x :=
  congrArg f (Function.leftInverse_invFun (bijective b p hp).1 x)

theorem edge_nil (f : Arrays (prime^b)) : edgeAction b [] f = f := by
  funext x
  exact edge_entry b [] (by intro op hop; exact (List.not_mem_nil hop).elim) f x

theorem run_append (p q : FieldProgram) (x : Shared50ModularExecution.Address (prime^b)) :
    AffineFieldProgram.run (specializes b (p++q)) x =
      AffineFieldProgram.run (specializes b q) (AffineFieldProgram.run (specializes b p) x) := by
  simp only [specializes,List.map_append,AffineFieldProgram.run,List.foldl_append]

theorem edge_append (p q : FieldProgram) (hp : Legal b p) (hq : Legal b q) (f : Arrays (prime^b)) :
    edgeAction b (p++q) f = edgeAction b q (edgeAction b p f) := by
  funext x
  obtain ⟨y,rfl⟩ := (bijective b (p++q) (legal_append b p q hp hq)).2 x
  rw [edge_entry b (p++q) (legal_append b p q hp hq),run_append,
    edge_entry b q hq,edge_entry b p hp]

def atom (a : Atom) (stored : World → Arrays (prime^b)) : World → Arrays (prime^b) := match a with
  | .field wire op => Function.update stored wire (edgeAction b [op] (stored wire))
  | .gate g => FramedCircuit.moduleGate g stored

def atoms (as : List Atom) (stored : World → Arrays (prime^b)) := as.foldl (fun stored a => atom b a stored) stored

def piece (p : Piece) (stored : World → Arrays (prime^b)) : World → Arrays (prime^b) := match p with
  | .segment seg => Function.update stored seg.wire (edgeAction b seg.ops (stored seg.wire))
  | .call wire i j => Function.update stored wire (edgeAction b [.interchange i j] (stored wire))
  | .gate g => FramedCircuit.moduleGate g.scalar stored

def run (ps : List Piece) (stored : World → Arrays (prime^b)) := ps.foldl (fun stored p => piece b p stored) stored

theorem atoms_append (as bs : List Atom) (stored : World → Arrays (prime^b)) :
    atoms b (as++bs) stored = atoms b bs (atoms b as stored) := List.foldl_append

/-- A complete attached field program is precisely its scalar atoms, in order. -/
theorem atoms_fields (wire : World) (ops : FieldProgram) (hp : Legal b ops) (stored : World → Arrays (prime^b)) :
    atoms b (ops.map (Atom.field wire)) stored = Function.update stored wire (edgeAction b ops (stored wire)) := by
  induction ops generalizing stored with
  | nil => simp only [List.map_nil,atoms,List.foldl_nil,edge_nil,Function.update_eq_self]
  | cons op ops ih =>
    have hhead : Legal b [op] := legal_sublist b _ _ hp (by intro x hx; exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hx)))
    have htail : Legal b ops := legal_sublist b _ _ hp (by intro x hx; exact List.mem_cons_of_mem _ hx)
    change atoms b (ops.map (Atom.field wire)) (Function.update stored wire (edgeAction b [op] (stored wire))) = _
    rw [ih htail,Function.update_self,Function.update_idem]
    rw [show op::ops = [op]++ops from rfl,edge_append b _ _ hhead htail]

/-- Every actual piece agrees with its retained literal atom expansion. -/
theorem piece_expand (p : Piece) (stored : World → Arrays (prime^b)) :
    atoms b (Shared50PieceSchedule.expandPiece p) stored = piece b p stored := by
  cases p with
  | segment seg =>
    exact atoms_fields b seg.wire seg.ops
      (legal_sublist b seg.parent seg.ops (legal_actual b seg.parent (Shared50OrderedPieces.segment_spec seg).1)
        (Shared50OrderedPieces.segment_spec seg).2.1) stored
  | call wire i j => rfl
  | gate g => rfl

theorem run_expand (ps : List Piece) (stored : World → Arrays (prime^b)) :
    run b ps stored = atoms b (ps.flatMap Shared50PieceSchedule.expandPiece) stored := by
  induction ps generalizing stored with
  | nil => rfl
  | cons p ps ih =>
    change run b ps (piece b p stored) = _
    rw [ih,List.flatMap_cons,atoms_append,piece_expand]

theorem control_expand (cs : List Control)
    (hc : ∀ wire p, FramedControlSchedule.Step.edge wire p ∈ cs → Legal b p)
    (stored : World → Arrays (prime^b)) :
    atoms b (cs.flatMap Shared50PieceSchedule.expandControl) stored =
      FramedControlSchedule.run (edgeAction b) cs stored := by
  induction cs generalizing stored with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons,atoms_append]
    cases c with
    | edge wire p =>
      rw [show Shared50PieceSchedule.expandControl (.edge wire p) = p.map (Atom.field wire) from rfl,
        atoms_fields b wire p (hc wire p List.mem_cons_self)]
      exact ih (fun wire p hp => hc wire p (List.mem_cons_of_mem _ hp)) _
    | gate g => exact ih (fun wire p hp => hc wire p (List.mem_cons_of_mem _ hp)) _

/-- Literal piece execution equals literal fixed interleaved control. -/
theorem run_fixed (stored : World → Arrays (prime^b)) :
    run b Shared50PieceSchedule.pieces stored =
      FramedControlSchedule.run (edgeAction b) Shared50FixedControl.control stored := by
  rw [run_expand,Shared50PieceSchedule.expansion_exact]
  apply control_expand
  intro wire p hp
  apply legal_actual
  have hh : p ∈ FramedControlSchedule.programs Shared50FixedControl.control :=
    List.mem_filterMap.mpr ⟨.edge wire p,hp,rfl⟩
  simpa only [Shared50FixedControl.programs_exact] using hh

/-- The full actual piece list realizes routed H/D transpose, including the
original dirty-scratch route, at every prime-power width. -/
theorem run_identity (stored : World → Arrays (prime^b)) :
    run b Shared50PieceSchedule.pieces stored =
      fun i a => stored (Shared50ShearEndpoints.route i) (a.2,a.1) := by
  rw [run_fixed,Shared50FixedControl.run_identity]

end
end IntegerMultBounds.Machine.Shared50PieceSemantics
