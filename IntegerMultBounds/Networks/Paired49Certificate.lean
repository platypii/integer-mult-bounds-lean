import IntegerMultBounds.Networks.Certificates.Paired49.Checked
import IntegerMultBounds.Networks.Certificates.Paired49.Outputs
import IntegerMultBounds.Networks.Certificates.Paired49.Unique
import IntegerMultBounds.Networks.Certificates.Paired49.Signatures
import IntegerMultBounds.Networks.DAGAllocatorBudget
import IntegerMultBounds.Networks.DAGCompileCorrect

/-! An unconditional finite witness for the 49-vertex pair-exclusion map.
The generator is untrusted: Lean checks all nodes, outputs and unique supports.
This proves the witness itself, not equality with the literal recursive builder.
The allocator budget counts physical scalar roles, not tape steps. -/

namespace IntegerMultBounds.Networks.Paired49Certificate

open DisjointCircuit MaskDAG
open Certificates.Paired49

attribute [local irreducible] entries outputs bank

def nodes : List (Node (Fin 1176)) := entries.map Entry.toNode

def outputRefs : List ℕ := outputs.map Prod.snd

theorem valid : Valid nodes := dag_valid

theorem node_count : nodes.length = 10989 := by
  simpa only [nodes, List.length_map] using entries_length

theorem additions : DAGAllocator.additionCount nodes = 9813 := by
  unfold DAGAllocator.additionCount nodes
  rw [List.countP_map]
  trans entries.countP (fun e => match e.kind with | .input _ => false | .add _ _ => true)
  · congr 1
    funext e
    simp only [Function.comp_apply, Entry.toNode]
    cases e.kind <;> rfl
  · exact addition_count

theorem output_count : outputRefs.length = 1176 := by
  simpa only [outputRefs, List.length_map] using Certificates.Paired49.output_count

theorem output_bounds : ∀ i ∈ outputRefs, i < nodes.length := by
  intro i hi
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hi
  rw [node_count]
  exact (output_spec entry he).1

/-- All 1176 requested pair-exclusion sums, with no acceptance premise. -/
theorem output_value {A : Type*} [AddCommMonoid A] (input : ℕ × ℕ → A)
    (entry : (ℕ × ℕ) × ℕ) (he : entry ∈ outputs) :
    (eval (fun i => input (PairMask.pairAt49 i)) nodes)[entry.2]? =
      some (supportSum input ((PairedCircuit.pairs (List.range 49)).toFinset.filter
        (fun p => p.1 ∉ [entry.1.1, entry.1.2] ∧
          p.2 ∉ [entry.1.1, entry.1.2]))) :=
  accepted_output_semantics input entries_checked entry he

theorem supports_unique : (nodes.map Node.support).Nodup := supports_nodup_certified

/-- Both endpoint summaries are exact for every node of the verified witness. -/
theorem endpoint_signatures :
    List.Forall₂ (MaskSignature.Correct signaturePayload) entries signatures :=
  (signatures_correct entries_checked).1

/-- The actual pruned compiler needs at most 9813 + 1176 scalar roles. -/
theorem allocated_roles : (DAGAllocator.compile nodes outputRefs).state.next ≤ 10989 := by
  have h := DAGAllocator.compile_roles_le nodes outputRefs valid output_bounds
  rw [additions, output_count] at h
  exact h

/-- Every designated output is a real role below this concrete budget. -/
theorem output_slot_bound (i : ℕ) (hi : i < 1176) :
    (DAGAllocator.compile nodes outputRefs).outputSlot i < 10989 := by
  apply Nat.lt_of_lt_of_le (DAGAllocator.compile_output_bound nodes outputRefs valid
    output_bounds i (by rwa [output_count])) allocated_roles

/-- Distinct requests receive distinct output roles. -/
theorem output_slots_distinct (i j : ℕ) (hi : i < 1176) (hj : j < 1176) (hne : i ≠ j) :
    (DAGAllocator.compile nodes outputRefs).outputSlot i ≠
      (DAGAllocator.compile nodes outputRefs).outputSlot j :=
  DAGAllocator.compile_output_ne nodes outputRefs valid output_bounds i j
    (by rwa [output_count]) (by rwa [output_count]) hne

end IntegerMultBounds.Networks.Paired49Certificate
