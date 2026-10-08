import IntegerMultBounds.Networks.Certificates.Shared50.Sound
import IntegerMultBounds.Networks.SharedPointOutputIndex

/-! The optimized fifty-copy witness, with every finite-count premise
discharged by ordinary kernel checks. These are scalar circuit bounds;
the rank-frame assembly and literal tape runtime remain separate obligations. -/

namespace IntegerMultBounds.Networks.Shared50Certificate

open DisjointCircuit NeighborCounts SharedPointReplay SharedPointExecution

attribute [local irreducible] SharedPointReplay.circuit

/-- Actual globally interned addition records, after certified duplicate sharing. -/
theorem addition_bound : DAGAllocator.additionCount circuit.nodes ≤ 450394 :=
  additions_le_supports.trans Certificates.Shared50.support_image_bound

/-- Physical roles allocated by the literal compiler, not an assigned cost. -/
theorem role_bound : code.state.next ≤ 509194 :=
  SharedPointExecution.role_bound Certificates.Shared50.support_image_bound

/-- Number of actual scalar XOR instructions emitted by the same compiler. -/
theorem instruction_bound : code.program.length ≤ 959588 :=
  SharedPointExecution.instruction_bound Certificates.Shared50.support_image_bound

/-- Correctness and both budgets hold for one and the same concrete program. -/
theorem scalar_certificate :
    code.state.next ≤ 509194 ∧ code.program.length ≤ 959588 ∧
      ∀ (input : Triple 50 → ZMod 2) (c : Fin 50) (j : Fin 1176),
        Circuit.run code.program (SharedPointExecution.initial input)
          (code.outputSlot (SharedPointOutputIndex.index c j)) =
          supportSum input (Finset.univ.filter
            (fun U : Triple 50 => U.val ∩ (embedding c j).val = {c})) :=
  ⟨role_bound, instruction_bound, SharedPointOutputIndex.run_partial_at⟩

theorem output_slot_bound (c : Fin 50) (j : Fin 1176) :
    code.outputSlot (SharedPointOutputIndex.index c j) < 509194 :=
  Nat.lt_of_lt_of_le (SharedPointExecution.output_slot_bound _
    (SharedPointOutputIndex.index_bound c j)) role_bound

end IntegerMultBounds.Networks.Shared50Certificate
