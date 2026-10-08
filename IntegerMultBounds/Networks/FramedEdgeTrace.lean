import IntegerMultBounds.Networks.FramedEmbedding
import IntegerMultBounds.Networks.DAGComplementExecution

/-! Ordered physical edge extraction preserves every frame change, including
identity changes and repeated incidences. Scalar instructions alone are omitted. -/

namespace IntegerMultBounds.Networks.FramedEdgeTrace

open FramedCircuit
variable {ι κ L R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

/-- Actual old/new frame pairs in physical instruction order. -/
def pairs (instructions : List (Instruction ι R E)) : List (Frame R E × Frame R E) :=
  instructions.filterMap fun instr => match instr with
    | .edge _ old next => some (old,next)
    | .gate _ => none

@[simp] theorem pairs_nil : pairs ([] : List (Instruction ι R E)) = [] := rfl

theorem pairs_append (left right : List (Instruction ι R E)) :
    pairs (left ++ right) = pairs left ++ pairs right := List.filterMap_append

@[simp] theorem pairs_gates (program : Circuit.Program ι R) :
    pairs (program.map (Instruction.gate (E := E))) = [] := by
  induction program with
  | nil => rfl
  | cons gate rest ih => simpa only [List.map_cons,pairs,List.filterMap_cons] using ih

/-- Finite bank restriction retains the exact ordered physical frame pairs. -/
theorem pairs_restrict (capacity : ℕ) (instructions : List (Instruction ℕ R E))
    (hb : BoundedFramedCircuit.Bounded capacity instructions) :
    pairs (BoundedFramedCircuit.restrict capacity instructions hb) = pairs instructions := by
  induction instructions with
  | nil => rfl
  | cons instr rest ih =>
    rw [BoundedFramedCircuit.restrict_cons]
    cases instr <;> simp only [BoundedFramedCircuit.finiteInstruction,pairs,List.filterMap_cons]
    · exact congrArg (List.cons _) (ih _)
    · exact ih _

/-- Injective physical placement does not change any old/new frame pair. -/
theorem pairs_embed (f : ι ↪ κ) (instructions : List (Instruction ι R E)) :
    pairs (FramedEmbedding.embed f instructions) = pairs instructions := by
  induction instructions with
  | nil => rfl
  | cons instr rest ih =>
    cases instr <;> simp only [FramedEmbedding.embed,List.map_cons,FramedEmbedding.instruction,
      pairs,List.filterMap_cons] at *
    · exact congrArg (List.cons _) ih
    · exact ih

variable [DecidableEq ι]

/-- The literal alignment instruction list realizes its ordered label trace. -/
theorem pairs_edges (frameOf : L → Frame R E) (current desired : ι → L) (wires : List ι) :
    pairs (FramedCircuit.edges (fun i => frameOf (current i)) (fun i => frameOf (desired i)) wires) =
      (RankTrace.edges current (wires.map fun i => (i,desired i))).map
        (fun p => (frameOf p.1,frameOf p.2)) := by
  induction wires generalizing current with
  | nil => rfl
  | cons i wires ih =>
    have he : Function.update (fun j => frameOf (current j)) i (frameOf (desired i)) =
        fun j => frameOf (Function.update current i (desired i) j) := by
      funext j; by_cases hj : j = i <;> simp [hj]
    simp only [FramedCircuit.edges,pairs,List.filterMap_cons,List.map_cons,RankTrace.edges,he]
    exact congrArg (List.cons _) (ih _)

end IntegerMultBounds.Networks.FramedEdgeTrace
