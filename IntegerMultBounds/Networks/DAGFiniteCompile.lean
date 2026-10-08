import IntegerMultBounds.Networks.BoundedCircuit
import IntegerMultBounds.Networks.DAGValueTransfer

/-! The actual role allocator emits a finite-register scalar program. Its bound
covers every elementary target and source, and restriction preserves execution
and instruction count exactly. -/

namespace IntegerMultBounds.Networks.DAGFiniteCompile

open DisjointCircuit DAGAllocator BoundedCircuit

private theorem add_bounded (capacity dst src : ℕ) (hd : dst < capacity) (hs : src < capacity) :
    GateBounded capacity (ReversibleFanout.add dst src) := by
  refine ⟨hd, ?_⟩
  intro term ht
  have he : term = (src, (1 : ZMod 2)) := by simpa [ReversibleFanout.add] using ht
  simpa only [he] using hs

/-- Bounds on an allocated fanout gate cover every scalar XOR it emits. -/
theorem gate_program_bounded (capacity : ℕ) (gate : DAGAllocator.Gate)
    (hl : gate.HasLayout) (hb : gate.Bounded capacity) : Bounded capacity gate.program := by
  obtain ⟨layout, hi, ho⟩ := hl
  have hp : layout.pivot < capacity := hb _ (List.mem_append_left _ (hi ▸ (by simp [ReversibleFanout.Layout.inputs])))
  rw [gate.program_eq_layout layout hi ho]
  intro scalar hs
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨src, hsrc, rfl⟩ := List.mem_map.mp hs
    exact add_bounded capacity _ _ hp
      (hb src (List.mem_append_left _ (hi ▸ (by simp [ReversibleFanout.Layout.inputs, hsrc]))))
  · obtain ⟨dst, hdst, rfl⟩ := List.mem_map.mp hs
    exact add_bounded capacity _ _
      (hb dst (List.mem_append_right _ (ho ▸ (by simp [ReversibleFanout.Layout.outputs, hdst])))) hp

variable {ι : Type*} [DecidableEq ι]

/-- A valid DAG's emitted elementary instructions mention only allocated roles. -/
theorem compile_program_bounded (nodes : List (Node ι)) (outputs : List ℕ)
    (hv : Valid nodes) (ho : ∀ i ∈ outputs, i < nodes.length) (capacity : ℕ)
    (hc : (compile nodes outputs).state.next ≤ capacity) :
    Bounded capacity (compile nodes outputs).program := by
  intro scalar hs
  obtain ⟨gate, hg, hs⟩ := List.mem_flatMap.mp hs
  have hb := compile_gates_bounded nodes outputs hv ho gate hg
  have hl := (compile_frontier nodes outputs hv ho).2.2 gate hg
  exact gate_program_bounded capacity gate hl (fun r hr => (hb r hr).trans_le hc) scalar hs

/-- A literal program over exactly the chosen finite register capacity. -/
def program (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (capacity : ℕ)
    (hc : (compile nodes outputs).state.next ≤ capacity) : Circuit.Program (Fin capacity) (ZMod 2) :=
  finiteProgram capacity (compile nodes outputs).program (compile_program_bounded nodes outputs hv ho capacity hc)

@[simp] theorem program_length (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (capacity : ℕ)
    (hc : (compile nodes outputs).state.next ≤ capacity) :
    (program nodes outputs hv ho capacity hc).length = (compile nodes outputs).program.length :=
  finiteProgram_length _ _ _

/-- Finite execution is the restriction of the original allocated execution. -/
theorem program_run (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (capacity : ℕ)
    (hc : (compile nodes outputs).state.next ≤ capacity) (state : ℕ → ZMod 2) :
    Circuit.run (program nodes outputs hv ho capacity hc) (fun i => state i.val) =
      fun i => Circuit.run (compile nodes outputs).program state i.val :=
  finiteProgram_run _ _ _ _

/-- Executing the literal reversed finite program restores every finite
register state, including states with arbitrary scratch contents. -/
theorem program_reverse_run (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (capacity : ℕ)
    (hc : (compile nodes outputs).state.next ≤ capacity) (state : Fin capacity → ZMod 2) :
    Circuit.run (program nodes outputs hv ho capacity hc).reverse
      (Circuit.run (program nodes outputs hv ho capacity hc) state) = state := by
  let full : ℕ → ZMod 2 := fun r => if hr : r < capacity then state ⟨r, hr⟩ else 0
  have he : (fun r : Fin capacity => full r.val) = state := by
    funext r
    simp [full, r.isLt]
  rw [← he, program_run]
  change Circuit.run (finiteProgram capacity (compile nodes outputs).program _).reverse _ = _
  rw [finiteProgram_reverse_run, compile_run_reverse nodes outputs hv ho]

/-- The actual requested output role as a finite register, with no fallback. -/
def outputSlot (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (capacity : ℕ)
    (hc : (compile nodes outputs).state.next ≤ capacity) (i : ℕ) (hi : i < outputs.length) : Fin capacity :=
  ⟨(compile nodes outputs).outputSlot i, (compile_output_bound nodes outputs hv ho i hi).trans_le hc⟩

/-- The finite-register program retains the actual input-preloaded DAG semantics. -/
theorem program_output (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (capacity : ℕ)
    (hc : (compile nodes outputs).state.next ≤ capacity) (input : ι → ZMod 2)
    (i : ℕ) (hi : i < outputs.length) :
    Circuit.run (program nodes outputs hv ho capacity hc)
      (fun r => DAGValueTransfer.initial (compile nodes outputs).sources
        (DAGValueTransfer.sourceInput nodes input) r.val)
      (outputSlot nodes outputs hv ho capacity hc i hi) =
        supportSum input (nodes[outputs[i]]'(ho _ (List.getElem_mem hi))).support := by
  rw [program_run]
  exact DAGValueTransfer.compile_output_input_value nodes outputs input hv ho i hi

end IntegerMultBounds.Networks.DAGFiniteCompile
