import IntegerMultBounds.Networks.GroupedModuleFrames

/-! Lower actual framed instructions to same-wire linear factors and unchanged
scalar gates. Product lists execute in reverse order because linear-map
multiplication composes right to left. Correctness concerns actual register
states; factor counts here are instruction counts, not tape runtimes. -/

namespace IntegerMultBounds.Networks.FramedFactorExecution

variable {ι R E : Type*} [DecidableEq ι] [CommRing R]
  [AddCommGroup E] [Module R E]

inductive Instruction (ι R E : Type*) [CommRing R] [AddCommGroup E] [Module R E] where
  | linear (wire : ι) (op : E →ₗ[R] E)
  | gate (g : Circuit.Gate ι R)

def execute : Instruction ι R E → (ι → E) → (ι → E)
  | .linear i op, x => Function.update x i (op (x i))
  | .gate g, x => FramedCircuit.moduleGate g x

def run : List (Instruction ι R E) → (ι → E) → (ι → E)
  | [], x => x
  | instr :: rest, x => run rest (execute instr x)

theorem run_append (p q : List (Instruction ι R E)) (x : ι → E) :
    run (p ++ q) x = run q (run p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons instr rest ih => exact ih _

/-- Place every factor on its original physical wire, in execution order. -/
def onWire (i : ι) (fs : List (E →ₗ[R] E)) : List (Instruction ι R E) :=
  fs.reverse.map (Instruction.linear i)

theorem run_onWire (i : ι) (fs : List (E →ₗ[R] E)) (x : ι → E) :
    run (onWire i fs) x = Function.update x i (fs.prod (x i)) := by
  induction fs with
  | nil => simp [onWire, run]
  | cons f fs ih =>
    rw [onWire, List.reverse_cons, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [run_append]
    change execute (.linear i f) (run (onWire i fs) x) = _
    rw [ih]
    simp only [execute, Function.update_self, Function.update_idem, List.prod_cons, Module.End.mul_apply]

/-- Factor lowering changes only the original edge's physical register. -/
theorem run_onWire_other (i j : ι) (hji : j ≠ i) (fs : List (E →ₗ[R] E)) (x : ι → E) :
    run (onWire i fs) x j = x j := by
  rw [run_onWire]
  exact Function.update_of_ne hji _ _

/-- Actual frame-change operators, extracted in program order and ignoring gates. -/
def edgeOperators : List (FramedCircuit.Instruction ι R E) → List (E →ₗ[R] E)
  | [] => []
  | .edge _ old next :: rest => (next.toLinearMap * old.symm.toLinearMap) :: edgeOperators rest
  | .gate _ :: rest => edgeOperators rest

omit [DecidableEq ι] in
/-- The generic lowering consumes the same ordered edge extraction as the
physical grouped compiler. -/
theorem edgeOperators_eq (p : List (FramedCircuit.Instruction ι R E)) :
    edgeOperators p = (GroupedModuleFrames.edgePairs p).map
      (fun e => e.2.toLinearMap * e.1.symm.toLinearMap) := by
  induction p with
  | nil => rfl
  | cons instr rest ih => cases instr <;> simp [edgeOperators, GroupedModuleFrames.edgePairs, ih]

omit [DecidableEq ι] in
/-- Certificates phrased directly over the grouped compiler's frame pairs
are accepted without reordering or choosing new edge operators. -/
theorem certificate_of_edgePairs (p : List (FramedCircuit.Instruction ι R E))
    (factors : List (List (E →ₗ[R] E)))
    (hf : List.Forall₂ (fun e fs => fs.prod = e.2.toLinearMap * e.1.symm.toLinearMap)
      (GroupedModuleFrames.edgePairs p) factors) :
    List.Forall₂ (fun op fs => fs.prod = op) (edgeOperators p) factors := by
  rwa [edgeOperators_eq, List.forall₂_map_left_iff]

/-- Consume one factor list for each actual edge; scalar gates consume none.
The correctness premise below guarantees that the supplied lists match exactly. -/
def lower : List (FramedCircuit.Instruction ι R E) → List (List (E →ₗ[R] E)) →
    List (Instruction ι R E)
  | [], _ => []
  | .edge i _ _ :: rest, fs => onWire i (fs.headD []) ++ lower rest fs.tail
  | .gate g :: rest, fs => .gate g :: lower rest fs

/-- Exact operator certificates suffice to refine every register state, including
scratch and spectators, throughout the entire ordered program. -/
theorem run_lower (p : List (FramedCircuit.Instruction ι R E))
    (factors : List (List (E →ₗ[R] E)))
    (hf : List.Forall₂ (fun op fs => fs.prod = op) (edgeOperators p) factors)
    (x : ι → E) : run (lower p factors) x = FramedCircuit.run p x := by
  induction p generalizing factors x with
  | nil => rfl
  | cons instr rest ih =>
    cases instr with
    | edge i old next =>
      cases hf with
      | cons hprod hrest =>
        simp only [lower, List.headD_cons, List.tail_cons, run_append, run_onWire,
          FramedCircuit.run, FramedCircuit.execute]
        rw [ih _ hrest, hprod]
        rfl
    | gate g =>
      exact ih factors hf (FramedCircuit.moduleGate g x)

def gates : List (Instruction ι R E) → List (Circuit.Gate ι R)
  | [] => []
  | .linear _ _ :: rest => gates rest
  | .gate g :: rest => g :: gates rest

def originalGates : List (FramedCircuit.Instruction ι R E) → List (Circuit.Gate ι R)
  | [] => []
  | .edge _ _ _ :: rest => originalGates rest
  | .gate g :: rest => g :: originalGates rest

omit [DecidableEq ι] in
@[simp] theorem gates_append (p q : List (Instruction ι R E)) :
    gates (p ++ q) = gates p ++ gates q := by
  induction p with
  | nil => rfl
  | cons instr rest ih => cases instr <;> simp [gates, ih]

omit [DecidableEq ι] in
@[simp] theorem gates_onWire (i : ι) (fs : List (E →ₗ[R] E)) : gates (onWire i fs) = [] := by
  unfold onWire
  generalize fs.reverse = gs
  induction gs with
  | nil => rfl
  | cons f gs ih => exact ih

omit [DecidableEq ι] in
/-- Scalar gate values and their order are literally retained. -/
theorem gates_lower (p : List (FramedCircuit.Instruction ι R E))
    (factors : List (List (E →ₗ[R] E))) : gates (lower p factors) = originalGates p := by
  induction p generalizing factors with
  | nil => rfl
  | cons instr rest ih => cases instr <;> simp [lower, gates, originalGates, ih]

def linearCount : List (Instruction ι R E) → ℕ
  | [] => 0
  | .linear _ _ :: rest => 1 + linearCount rest
  | .gate _ :: rest => linearCount rest

omit [DecidableEq ι] in
@[simp] theorem linearCount_append (p q : List (Instruction ι R E)) :
    linearCount (p ++ q) = linearCount p + linearCount q := by
  induction p with
  | nil => simp [linearCount]
  | cons instr rest ih => cases instr <;> simp [linearCount, ih, Nat.add_assoc]

omit [DecidableEq ι] in
@[simp] theorem linearCount_onWire (i : ι) (fs : List (E →ₗ[R] E)) :
    linearCount (onWire i fs) = fs.length := by
  have aux (gs : List (E →ₗ[R] E)) :
      linearCount (gs.map (Instruction.linear i)) = gs.length := by
    induction gs with
    | nil => rfl
    | cons f gs ih => simp [linearCount, ih, Nat.add_comm]
  simpa [onWire] using aux fs.reverse

omit [DecidableEq ι] in
/-- The exact number of executed linear-factor instructions is the certificate
list's aggregate length; zero-factor edges introduce no instruction. -/
theorem linearCount_lower (p : List (FramedCircuit.Instruction ι R E))
    (factors : List (List (E →ₗ[R] E)))
    (hf : List.Forall₂ (fun op fs => fs.prod = op) (edgeOperators p) factors) :
    linearCount (lower p factors) = (factors.map List.length).sum := by
  induction p generalizing factors with
  | nil => cases hf; rfl
  | cons instr rest ih =>
    cases instr with
    | edge i old next =>
      cases hf with
      | cons hprod hrest =>
        simp [lower, ih _ hrest]
    | gate g => exact ih factors hf

omit [DecidableEq ι] in
/-- Every lowered instruction is either one linear factor or one scalar gate. -/
theorem length_eq (p : List (Instruction ι R E)) :
    p.length = linearCount p + (gates p).length := by
  induction p with
  | nil => rfl
  | cons instr rest ih => cases instr <;> simp [linearCount, gates, ih] <;> omega

omit [DecidableEq ι] in
@[simp] theorem originalGates_append (p q : List (FramedCircuit.Instruction ι R E)) :
    originalGates (p ++ q) = originalGates p ++ originalGates q := by
  induction p with
  | nil => rfl
  | cons instr rest ih => cases instr <;> simp [originalGates, ih]

omit [DecidableEq ι] in
@[simp] theorem originalGates_map (gs : Circuit.Program ι R) :
    originalGates (E := E) (gs.map FramedCircuit.Instruction.gate) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [originalGates, ih]

@[simp] theorem originalGates_edges (current desired : ι → FramedCircuit.Frame R E)
    (wires : List ι) : originalGates (FramedCircuit.edges current desired wires) = [] := by
  induction wires generalizing current with
  | nil => rfl
  | cons i wires ih => simp [FramedCircuit.edges, originalGates, ih]

section Grouped
variable {L : Type*} [DecidableEq R]

@[simp] theorem originalGates_compileFramed (g : GroupedCircuit.Group ι R)
    (current : ι → FramedCircuit.Frame R E) (D : FramedCircuit.Frame R E) :
    originalGates (GroupedCircuit.compileFramed g current D) = GroupedCircuit.compile g := by
  simp [GroupedCircuit.compileFramed]

/-- Erasing frame changes yields exactly the fixed compiled scalar schedule. -/
theorem originalGates_compile (frameOf : L → FramedCircuit.Frame R E)
    (current : ι → L) (vs : List (GroupedFrames.Vertex ι L R)) :
    originalGates (GroupedModuleFrames.compile frameOf current vs) =
      GroupedCircuit.compileGroups (vs.map GroupedFrames.Vertex.group) := by
  induction vs generalizing current with
  | nil => rfl
  | cons v vs ih =>
    simp [GroupedModuleFrames.compile, ih, GroupedCircuit.compileGroups]

/-- Sink alignment contributes no scalar gates, so the physical module
network retains the same scalar schedule independently of its frame module. -/
theorem originalGates_network (frameOf : L → FramedCircuit.Frame R E)
    (wires : List ι) (input output : ι → L) (vs : List (GroupedFrames.Vertex ι L R)) :
    originalGates (GroupedModuleFrames.network frameOf wires input output vs) =
      GroupedCircuit.compileGroups (vs.map GroupedFrames.Vertex.group) := by
  simp [GroupedModuleFrames.network, originalGates_compile]

/-- Exact total length after lowering: all placed factors plus the unchanged
scalar gates, with no count assigned to nonexistent instructions. -/
theorem length_lower_network (frameOf : L → FramedCircuit.Frame R E)
    (wires : List ι) (input output : ι → L) (vs : List (GroupedFrames.Vertex ι L R))
    (factors : List (List (E →ₗ[R] E)))
    (hf : List.Forall₂ (fun op fs => fs.prod = op)
      (edgeOperators (GroupedModuleFrames.network frameOf wires input output vs)) factors) :
    (lower (GroupedModuleFrames.network frameOf wires input output vs) factors).length =
      (factors.map List.length).sum +
        (GroupedCircuit.compileGroups (vs.map GroupedFrames.Vertex.group)).length := by
  rw [length_eq, linearCount_lower _ _ hf, gates_lower, originalGates_network]

end Grouped
end IntegerMultBounds.Networks.FramedFactorExecution
