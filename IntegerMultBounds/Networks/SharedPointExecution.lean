import IntegerMultBounds.Networks.SharedPointReplay
import IntegerMultBounds.Networks.SharedPointOutputMap
import IntegerMultBounds.Networks.DAGValueTransfer

/-! Scalar execution of the actual globally interned circuit. The concrete
allocated program computes every common-point partial intersection sum and
has an executable inverse on arbitrary register states. -/

namespace IntegerMultBounds.Networks.SharedPointExecution

open DisjointCircuit NeighborCounts SharedPointReplay

attribute [local irreducible] SharedPointReplay.circuit Paired49Certificate.nodes
  Certificates.Paired49.entries Certificates.Paired49.outputs Certificates.Paired49.bank

/-- The program emitted by the allocator for the actual fifty-copy replay. -/
def code : DAGAllocator.Code := DAGAllocator.compile circuit.nodes outputRefs

/-- Initialize actual physical sources with their triple input values. -/
def initial (input : Triple 50 → ZMod 2) : ℕ → ZMod 2 :=
  DAGValueTransfer.initial code.sources (DAGValueTransfer.sourceInput circuit.nodes input)

/-- Every physical output computes its certified lifted exclusion support. -/
theorem run_output (input : Triple 50 → ZMod 2) (i : ℕ) (hi : i < circuit.outputs.length) :
    Circuit.run code.program (initial input) (code.outputSlot i) =
      supportSum input (expected circuit.outputs[i]) := by
  have hi' : i < outputRefs.length := by simpa only [outputRefs, List.length_map] using hi
  have hb := output_bound circuit.outputs[i] (List.getElem_mem hi)
  have hs := output_support circuit.outputs[i] (List.getElem_mem hi)
  simp only [CorrectOutput, List.getElem?_map, List.getElem?_eq_getElem hb, Option.map_some] at hs
  have hr := DAGValueTransfer.compile_output_input_value circuit.nodes outputRefs input
    valid outputRefs_bounds i hi'
  simp only [outputRefs, List.getElem_map] at hr
  exact hr.trans (congrArg (supportSum input) (Option.some.inj hs))

/-- All pairs of a common point and a canonical local pair have designated
outputs in the constructed program, independently of support sharing. -/
theorem output_covers (c : Fin 50) (j : Fin 1176) :
    ∃ i, ∃ hi : i < circuit.outputs.length,
      circuit.outputs[i].common = c ∧ circuit.outputs[i].pair = PairMask.pairAt 49 j := by
  have hm : (c, PairMask.pairAt 49 j) ∈ circuit.outputs.map key := by
    rw [output_keys]
    apply List.mem_flatMap.mpr
    refine ⟨c, List.mem_finRange c, ?_⟩
    exact List.mem_map.mpr ⟨PairMask.pairAt 49 j, PairMask.pairAt_mem 49 j, rfl⟩
  obtain ⟨out, ho, hk⟩ := List.mem_map.mp hm
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ho
  exact ⟨i, hi, by simpa only [he, key] using congrArg Prod.fst hk,
    by simpa only [he, key] using congrArg Prod.snd hk⟩

/-- The actual scalar outputs are the full shared-point partial sums over
all triples meeting the requested triple in precisely the common point. -/
theorem run_partial (input : Triple 50 → ZMod 2) (c : Fin 50) (j : Fin 1176) :
    ∃ i, ∃ hi : i < circuit.outputs.length,
      circuit.outputs[i].common = c ∧ circuit.outputs[i].pair = PairMask.pairAt 49 j ∧
      Circuit.run code.program (initial input) (code.outputSlot i) =
        supportSum input (Finset.univ.filter (fun T : Triple 50 =>
          T.val ∩ (embedding c j).val = {c})) := by
  obtain ⟨i, hi, hc, hp⟩ := output_covers c j
  refine ⟨i, hi, hc, hp, ?_⟩
  rw [run_output input i hi, expected, hc, hp]
  exact congrArg (supportSum input) (SharedPointOutputMap.lifted_exclusion 49 c j)

/-- Coverage also holds in the intrinsic triple indexing, without assuming
a caller already possesses an inverse pair index. -/
theorem run_partial_triple (input : Triple 50 → ZMod 2) (c : Fin 50)
    (T : Triple 50) (hc : c ∈ T.val) :
    ∃ i, ∃ hi : i < circuit.outputs.length,
      circuit.outputs[i].common = c ∧
      Circuit.run code.program (initial input) (code.outputSlot i) =
        supportSum input (Finset.univ.filter (fun U : Triple 50 => U.val ∩ T.val = {c})) := by
  obtain ⟨j, hj⟩ := SharedPointOutputMap.source_covers 49 c T hc
  obtain ⟨i, hi, hcommon, _, hrun⟩ := run_partial input c j
  refine ⟨i, hi, hcommon, ?_⟩
  have he : embedding c j = T := hj
  simpa only [he] using hrun

/-- Every requested output has a bounded physical register. -/
theorem output_slot_bound (i : ℕ) (hi : i < 58800) : code.outputSlot i < code.state.next :=
  DAGAllocator.compile_output_bound circuit.nodes outputRefs valid outputRefs_bounds i
    (by rwa [outputRefs_count])

/-- Distinct output requests occupy distinct physical registers. -/
theorem output_slots_distinct (i j : ℕ) (hi : i < 58800) (hj : j < 58800) (hne : i ≠ j) :
    code.outputSlot i ≠ code.outputSlot j :=
  DAGAllocator.compile_output_ne circuit.nodes outputRefs valid outputRefs_bounds i j
    (by rwa [outputRefs_count]) (by rwa [outputRefs_count]) hne

/-- The emitted program has an executable inverse on every register state. -/
theorem reverse_run (state : ℕ → ZMod 2) :
    Circuit.run code.program.reverse (Circuit.run code.program state) = state :=
  DAGAllocator.compile_run_reverse circuit.nodes outputRefs valid outputRefs_bounds state

theorem role_bound
    (hcard : (SharedPointFamily.domain.image SharedPointFamily.support).card ≤ 450394) :
    code.state.next ≤ 509194 := allocated_roles_le hcard

theorem instruction_bound
    (hcard : (SharedPointFamily.domain.image SharedPointFamily.support).card ≤ 450394) :
    code.program.length ≤ 959588 := compiled_instructions_le hcard

end IntegerMultBounds.Networks.SharedPointExecution
