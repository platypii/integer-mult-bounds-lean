import IntegerMultBounds.Networks.FramedControlSchedule
import IntegerMultBounds.Networks.Shared50AffineControl
import IntegerMultBounds.Networks.AffineFieldSegments

/-! Role-preserving attachment of the actual rational field schedules to the
complete modular framed execution. Scalar gates remain at their original
positions between edges. This exposes exact instruction order and semantics;
it does not yet assert width independence of the interleaved control list. -/
namespace IntegerMultBounds.Networks.Shared50OrderedControl
noncomputable section
attribute [local irreducible] Shared50Finite.program SharedPointReplay.circuit SharedPointExecution.code
  Shared50GlobalCircuit.program50 Shared50GlobalCircuit.program Shared50GlobalCircuit.enumeration
  Shared50FiniteInterchange.program Shared50AffineControl.rationalSchedules Shared50AffineControl.schedules
  Shared50ModularExecution.program
open Shared50ModularSchedule (Index)
open Shared50ModularControl (prime)
open Shared50GlobalBudget (World)
open Shared50ModularExecution (Address Arrays)
open Shared50AffineControl (rationalSchedules)
open FramedControlSchedule

abbrev FieldProgram := List (AffineFieldProgram.Op Index ℚ)
abbrev Control := Step World (ZMod 2) FieldProgram

def specializes (b : ℕ) (p : FieldProgram) :=
  p.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (prime^b)))

def Realizes (b : ℕ) (edge : FramedCircuit.Frame (ZMod 2) (Arrays (prime^b)) ×
    FramedCircuit.Frame (ZMod 2) (Arrays (prime^b))) (p : FieldProgram) : Prop :=
  Shared50AffineControl.EdgeRealizes (prime^b) edge (specializes b p)

theorem edge_certificate (b : ℕ) :
    List.Forall₂ (Realizes b)
      (FramedEdgeTrace.pairs (Shared50FiniteInterchange.program (prime^b))) rationalSchedules := by
  have h := Shared50AffineControl.physical_realizes b
  rw [Shared50AffineControl.schedules_eq_map,List.forall₂_map_right_iff] at h
  exact h

/-- Each attached field program retains its actual wire and scalar-gate neighbors. -/
def schedule (b : ℕ) : List Control :=
  attach (Shared50FiniteInterchange.program (prime^b)) rationalSchedules

theorem instruction_matches (b : ℕ) :
    List.Forall₂ (Matches (Realizes b)) (schedule b)
      (Shared50FiniteInterchange.program (prime^b)) :=
  attach_matches _ _ _ (edge_certificate b)

theorem programs_exact (b : ℕ) : programs (schedule b) = rationalSchedules :=
  programs_attach _ _ _ (edge_certificate b)

private theorem erase_moveAll {A : Type*} (is : List World) (move : A ≃ A) :
    BoundedFramedCircuit.erase (Shared50FiniteInterchange.moveAll is move) = [] := by
  induction is with
  | nil => rfl
  | cons i is ih => exact ih

private theorem erase_around {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (left middle right : List (FramedCircuit.Instruction World (ZMod 2) E))
    (hl : BoundedFramedCircuit.erase left = []) (hr : BoundedFramedCircuit.erase right = []) :
    BoundedFramedCircuit.erase (left ++ middle ++ right) = BoundedFramedCircuit.erase middle := by
  simp only [Shared50FramedInvocation.erase_append,hl,hr,List.nil_append,List.append_nil]

/-- Every original pointwise gate survives, in order; surrounding edges add none. -/
theorem gates_exact (b : ℕ) : gates (schedule b) = Shared50GlobalCircuit.program50 := by
  calc
    gates (schedule b) = BoundedFramedCircuit.erase
        (Shared50FiniteInterchange.program (prime^b)) := gates_attach _ _
    _ = BoundedFramedCircuit.erase
        (Shared50ModularExecution.program (prime^b) Shared50GlobalCircuit.enumeration) :=
      by
        unfold Shared50FiniteInterchange.program
        exact erase_around _ _ _ (erase_moveAll _ _) (erase_moveAll _ _)
    _ = Shared50GlobalCircuit.program50 := by
      unfold Shared50GlobalCircuit.program50
      exact Shared50ModularExecution.scalar_erasure _ _

/-- Semantic evaluator only: the inverse is justified by the actual edge
certificate below, and is not being treated as a unit-cost machine operation. -/
def edgeAction (b : ℕ) (p : FieldProgram) (f : Arrays (prime^b)) : Arrays (prime^b) :=
  fun a => f (Function.invFun (AffineFieldProgram.run (specializes b p)) a)

theorem edgeAction_eq (b : ℕ) (old next : FramedCircuit.Frame (ZMod 2) (Arrays (prime^b)))
    (p : FieldProgram) (h : Realizes b (old,next) p) (f : Arrays (prime^b)) :
    edgeAction b p f = next (old.symm f) := by
  obtain ⟨move,hr,hframe⟩ := h
  have he : AffineFieldProgram.run (specializes b p) = move := funext hr
  have hi : Function.invFun (move : Address (prime^b) → Address (prime^b)) = move.symm :=
    Function.invFun_eq_of_injective_of_rightInverse move.injective move.apply_symm_apply
  apply Eq.trans ?_ (hframe f).symm
  unfold edgeAction
  rw [he,hi]

/-- The interleaved, role-specific rational control realizes full address
interchange and the original data route, including arbitrary dirty scratch. -/
theorem run_identity (b : ℕ) (stored : World → Arrays (prime^b)) :
    FramedControlSchedule.run (edgeAction b) (schedule b) stored =
      fun i a => stored (Shared50ShearEndpoints.route i) (a.2,a.1) := by
  rw [run_eq _ (Realizes b) (edgeAction_eq b) _ _ (instruction_matches b)]
  exact Shared50FiniteInterchange.program_identity b stored

private theorem interchanges_map {R S : Type*} (f : R → S)
    (p : List (AffineFieldProgram.Op Index R)) :
    AffineFieldProgram.interchanges (p.map (AffineFieldProgram.mapOp f)) =
      AffineFieldProgram.interchanges p := by
  induction p with
  | nil => rfl
  | cons op p ih =>
    cases op with
    | interchange i j =>
      change AffineFieldProgram.interchanges (p.map (AffineFieldProgram.mapOp f)) + 1 =
        AffineFieldProgram.interchanges p + 1
      exact congrArg (· + 1) ih
    | affineH op => exact ih
    | affineD op => exact ih
    | addToD i j => exact ih
    | subFromD i j => exact ih

/-- Recursive boundaries are counted in the literal attached edge programs. -/
def calls (s : List Control) : ℕ :=
  ((programs s).map fun p => AffineFieldSegments.recursiveCalls (AffineFieldSegments.split p)).sum

theorem calls_exact (b : ℕ) : calls (schedule b) = Shared50Parameters.s := by
  have h := Shared50AffineControl.interchanges_exact (prime^b)
  rw [Shared50AffineControl.schedules_eq_map] at h
  simpa only [calls,programs_exact,AffineFieldSegments.split_recursiveCalls,
    List.map_map,Function.comp_def,interchanges_map] using h

/-- Every actual nonrecursive run has the exact premises of the existing clean
physical segment compiler; its role is retained by the enclosing edge step. -/
theorem segment_spec (b : ℕ) (wire : World) (p : FieldProgram)
    (hp : Step.edge wire p ∈ schedule b) (ops : FieldProgram)
    (hops : ops ∈ AffineFieldSegments.runs (AffineFieldSegments.split p)) :
    p ∈ rationalSchedules ∧ (∀ op ∈ ops, op ∈ p) ∧
      (∀ op ∈ ops, AffineFieldCoordinates.Nonrecursive op) := by
  have hm : p ∈ programs (schedule b) :=
    List.mem_filterMap.mpr ⟨.edge wire p,hp,rfl⟩
  rw [programs_exact] at hm
  exact ⟨hm,AffineFieldSegments.split_run_spec p ops hops⟩

end
end IntegerMultBounds.Networks.Shared50OrderedControl
