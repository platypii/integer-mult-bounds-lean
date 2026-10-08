import IntegerMultBounds.Networks.Paired49Certificate
import IntegerMultBounds.Networks.DAGValueTransfer

/-! The checked local witness compiled to its actual scalar register program.
Preloading the physical input roles and zeroing other roles gives the complete
pair-exclusion map. This is scalar execution, not literal tape execution. -/

namespace IntegerMultBounds.Networks.Paired49Execution

open DisjointCircuit Paired49Certificate
open Certificates.Paired49

attribute [local irreducible] entries outputs bank

/-- The literal program and its source/output allocation. -/
def code : DAGAllocator.Code := DAGAllocator.compile nodes outputRefs

/-- Load actual input labels into their distinct physical source roles. -/
def initial (input : ℕ × ℕ → ZMod 2) : ℕ → ZMod 2 :=
  DAGValueTransfer.initial code.sources
    (DAGValueTransfer.sourceInput nodes (fun i => input (PairMask.pairAt49 i)))

/-- Every requested output of the actual emitted program is its exclusion sum. -/
theorem run_output (input : ℕ × ℕ → ZMod 2) (i : ℕ) (hi : i < outputs.length) :
    Circuit.run code.program (initial input) (code.outputSlot i) =
      supportSum input ((PairedCircuit.pairs (List.range 49)).toFinset.filter
        (fun p => p.1 ∉ [(outputs[i]).1.1, (outputs[i]).1.2] ∧
          p.2 ∉ [(outputs[i]).1.1, (outputs[i]).1.2])) := by
  have hi' : i < outputRefs.length := by simpa only [outputRefs, List.length_map] using hi
  have hb : (outputs[i]).2 < nodes.length := by
    rw [node_count]
    exact (output_spec (outputs[i]) (List.getElem_mem hi)).1
  have hs := Paired49Certificate.output_value input (outputs[i]) (List.getElem_mem hi)
  rw [eval_eq _ _ valid, List.getElem?_map, List.getElem?_eq_getElem hb,
    Option.map_some] at hs
  have hrun := DAGValueTransfer.compile_output_input_value nodes outputRefs
    (fun j => input (PairMask.pairAt49 j)) valid output_bounds i hi'
  simp only [outputRefs, List.getElem_map] at hrun
  exact hrun.trans (Option.some.inj hs)

theorem role_bound : code.state.next ≤ 10989 := allocated_roles

/-- The same concrete program is reversible even away from clean inputs. -/
theorem reverse_run (state : ℕ → ZMod 2) :
    Circuit.run code.program.reverse (Circuit.run code.program state) = state :=
  DAGAllocator.compile_run_reverse nodes outputRefs valid output_bounds state

end IntegerMultBounds.Networks.Paired49Execution
