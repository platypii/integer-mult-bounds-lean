import IntegerMultBounds.Networks.FramedEdgeTrace

/-! Attach edge implementations without dropping wire names or moving scalar
instructions. The ordered relation checks every literal original instruction;
its edge-only projection is the existing physical edge certificate. -/
namespace IntegerMultBounds.Networks.FramedControlSchedule
open FramedCircuit
variable {ι R E P : Type*} [CommRing R] [AddCommGroup E] [Module R E]

inductive Step (ι R P : Type*) where
  | edge (wire : ι) (program : P)
  | gate (g : Circuit.Gate ι R)

/-- A total zipper. Theorems require the complete edge certificate, which
excludes exhausting the implementation list before the physical edges. -/
def attach : List (Instruction ι R E) → List P → List (Step ι R P)
  | [], _ => []
  | .gate g :: rest, ps => .gate g :: attach rest ps
  | .edge i _ _ :: rest, p :: ps => .edge i p :: attach rest ps
  | .edge _ _ _ :: rest, [] => attach rest []

def programs (s : List (Step ι R P)) : List P :=
  s.filterMap fun step => match step with
    | .edge _ p => some p
    | .gate _ => none

def gates (s : List (Step ι R P)) : Circuit.Program ι R :=
  s.filterMap fun step => match step with
    | .edge _ _ => none
    | .gate g => some g

/-- The wire and gate are identical to those in the actual instruction;
only the opaque frame pair is replaced by its certified implementation. -/
inductive Matches (rel : (Frame R E × Frame R E) → P → Prop) :
    Step ι R P → Instruction ι R E → Prop
  | edge (i old next p) (h : rel (old,next) p) :
      Matches rel (.edge i p) (.edge i old next)
  | gate (g) : Matches rel (.gate g) (.gate g)

/-- No edge, gate, role, or relative position is lost. -/
theorem attach_matches (rel : (Frame R E × Frame R E) → P → Prop)
    (instructions : List (Instruction ι R E)) (ps : List P)
    (h : List.Forall₂ rel (FramedEdgeTrace.pairs instructions) ps) :
    List.Forall₂ (Matches rel) (attach instructions ps) instructions := by
  induction instructions generalizing ps with
  | nil => exact .nil
  | cons instr rest ih =>
    cases instr with
    | gate g => exact .cons (.gate g) (ih ps h)
    | edge i old next =>
      cases h with
      | cons hp ht => exact .cons (.edge i old next _ hp) (ih _ ht)

/-- Erasing attached edge implementations recovers the exact scalar list. -/
theorem gates_attach (instructions : List (Instruction ι R E)) (ps : List P) :
    gates (attach instructions ps) = BoundedFramedCircuit.erase instructions := by
  induction instructions generalizing ps with
  | nil => rfl
  | cons instr rest ih =>
    cases instr with
    | gate g => simpa only [attach,gates,List.filterMap_cons,BoundedFramedCircuit.erase]
        using congrArg (List.cons g) (ih ps)
    | edge i old next => cases ps <;> exact ih _

/-- The exact ordered implementation list survives the role-preserving zipper. -/
theorem programs_attach (rel : (Frame R E × Frame R E) → P → Prop)
    (instructions : List (Instruction ι R E)) (ps : List P)
    (h : List.Forall₂ rel (FramedEdgeTrace.pairs instructions) ps) :
    programs (attach instructions ps) = ps := by
  induction instructions generalizing ps with
  | nil => cases h; rfl
  | cons instr rest ih =>
    cases instr with
    | gate g => exact ih ps h
    | edge i old next =>
      cases h with
      | cons hp ht => exact congrArg (List.cons _) (ih _ ht)

variable [DecidableEq ι]

def execute (edge : P → E → E) : Step ι R P → (ι → E) → (ι → E)
  | .edge i p, x => Function.update x i (edge p (x i))
  | .gate g, x => moduleGate g x

def run (edge : P → E → E) : List (Step ι R P) → (ι → E) → (ι → E)
  | [], x => x
  | step :: rest, x => run edge rest (execute edge step x)

/-- Ordered implementation semantics agree with the original framed execution.
This is a semantic bridge, not a claim that `edge` has a tape implementation. -/
theorem run_eq (edge : P → E → E)
    (rel : (Frame R E × Frame R E) → P → Prop)
    (hrel : ∀ old next p, rel (old,next) p → ∀ x, edge p x = next (old.symm x))
    (s : List (Step ι R P)) (instructions : List (Instruction ι R E))
    (h : List.Forall₂ (Matches rel) s instructions) (x : ι → E) :
    run edge s x = FramedCircuit.run instructions x := by
  induction h generalizing x with
  | nil => rfl
  | cons hs ht ih =>
    cases hs with
    | gate g => exact ih _
    | edge i old next p hp =>
      simpa only [run,execute,FramedCircuit.run_cons,FramedCircuit.execute,hrel old next p hp]
        using ih (Function.update x i (next (old.symm (x i))))

end IntegerMultBounds.Networks.FramedControlSchedule
