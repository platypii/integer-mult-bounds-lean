import IntegerMultBounds.Networks.FramedControlSchedule

/-! Width-independent control shapes retain every wire and scalar gate, while
forgetting only the old/new frame operators. -/
namespace IntegerMultBounds.Networks.FramedControlShape
open FramedCircuit FramedControlSchedule
variable {ι κ R E F : Type*} [CommRing R] [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F]

/-- Exact control shape: identity edges and repeated edges are retained. -/
def shape (instructions : List (Instruction ι R E)) : List (Step ι R Unit) :=
  instructions.map fun instr => match instr with
    | .edge i _ _ => .edge i ()
    | .gate g => .gate g

@[simp] theorem shape_append (p q : List (Instruction ι R E)) :
    shape (p++q) = shape p ++ shape q := List.map_append

@[simp] theorem shape_gates (p : Circuit.Program ι R) :
    shape (p.map (Instruction.gate (E := E))) = p.map Step.gate := by
  simp only [shape,List.map_map,Function.comp_def]

/-- Matching shapes suffice to attach identical field code in identical slots. -/
theorem attach_eq {P : Type*} (p : List (Instruction ι R E)) (q : List (Instruction ι R F))
    (h : shape p = shape q) (ps : List P) : attach p ps = attach q ps := by
  induction p generalizing q ps with
  | nil => cases q with
    | nil => rfl
    | cons instr q => cases h
  | cons instr p ih =>
    cases q with
    | nil => cases h
    | cons instr' q =>
      cases instr <;> cases instr' <;>
        simp only [shape,List.map_cons,List.cons.injEq,Step.edge.injEq,Step.gate.injEq,
          reduceCtorEq,false_and] at h
      · obtain ⟨⟨rfl,_⟩,ht⟩ := h
        cases ps <;> simp only [attach,ih q ht]
      · obtain ⟨rfl,ht⟩ := h
        exact congrArg (List.cons _) (ih q ht ps)

@[simp] theorem shape_edges [DecidableEq ι] (current desired : ι → Frame R E) (wires : List ι) :
    shape (edges current desired wires) = wires.map (fun i => Step.edge i ()) := by
  induction wires generalizing current with
  | nil => rfl
  | cons i wires ih => simpa only [edges,shape,List.map_cons] using congrArg (List.cons _) (ih _)

def rename (f : ι ↪ κ) : Step ι R Unit → Step κ R Unit
  | .edge i _ => .edge (f i) ()
  | .gate g => .gate (GlobalCircuit.embedGate f g)

@[simp] theorem shape_embed (f : ι ↪ κ) (p : List (Instruction ι R E)) :
    shape (FramedEmbedding.embed f p) = (shape p).map (rename f) := by
  induction p with
  | nil => rfl
  | cons instr p ih =>
    cases instr <;>
      simpa only [FramedEmbedding.embed,List.map_cons,FramedEmbedding.instruction,shape,rename]
      using congrArg (List.cons _) ih

/-- Finite restriction depends on bounded wire/gate names, never frame values. -/
theorem shape_restrict_eq (capacity : ℕ) (p : List (Instruction ℕ R E))
    (q : List (Instruction ℕ R F)) (hp : BoundedFramedCircuit.Bounded capacity p)
    (hq : BoundedFramedCircuit.Bounded capacity q) (h : shape p = shape q) :
    shape (BoundedFramedCircuit.restrict capacity p hp) =
      shape (BoundedFramedCircuit.restrict capacity q hq) := by
  induction p generalizing q with
  | nil => cases q with
    | nil => rfl
    | cons instr q => cases h
  | cons instr p ih =>
    cases q with
    | nil => cases h
    | cons instr' q =>
      rw [BoundedFramedCircuit.restrict_cons,BoundedFramedCircuit.restrict_cons]
      cases instr <;> cases instr' <;>
        simp only [shape,List.map_cons,List.cons.injEq,Step.edge.injEq,Step.gate.injEq,
          reduceCtorEq,false_and] at h
      · obtain ⟨⟨rfl,_⟩,ht⟩ := h
        exact congrArg (List.cons _) (ih _ _ _ ht)
      · obtain ⟨rfl,ht⟩ := h
        exact congrArg (List.cons _) (ih _ _ _ ht)

end IntegerMultBounds.Networks.FramedControlShape
