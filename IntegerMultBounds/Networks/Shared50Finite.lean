import IntegerMultBounds.Networks.Shared50Certificate
import IntegerMultBounds.Networks.DAGFiniteCompile

/-! One concrete finite-register program realizes the optimized shared-point
map within its certified storage and scalar-instruction budgets. -/

namespace IntegerMultBounds.Networks.Shared50Finite

open DisjointCircuit NeighborCounts SharedPointReplay

attribute [local irreducible] SharedPointReplay.circuit

private theorem capacity_bound :
    (DAGAllocator.compile circuit.nodes outputRefs).state.next ≤ 509194 :=
  Shared50Certificate.role_bound

/-- The actual compiler's program restricted to the certified finite role bank. -/
def program : Circuit.Program (Fin 509194) (ZMod 2) :=
  DAGFiniteCompile.program circuit.nodes outputRefs valid outputRefs_bounds
    509194 capacity_bound

def initial (input : Triple 50 → ZMod 2) (role : Fin 509194) : ZMod 2 :=
  SharedPointExecution.initial input role.val

/-- Concrete arithmetic addressing followed by the actual allocated role lookup. -/
def output (c : Fin 50) (j : Fin 1176) : Fin 509194 :=
  ⟨SharedPointExecution.code.outputSlot (SharedPointOutputIndex.index c j),
    Shared50Certificate.output_slot_bound c j⟩

theorem instruction_bound : program.length ≤ 959588 := by
  rw [program, DAGFiniteCompile.program_length]
  exact Shared50Certificate.instruction_bound

/-- Exact partial-map semantics on an actual finite register state. -/
theorem run_output (input : Triple 50 → ZMod 2) (c : Fin 50) (j : Fin 1176) :
    Circuit.run program (initial input) (output c j) =
      supportSum input (Finset.univ.filter
        (fun U : Triple 50 => U.val ∩ (embedding c j).val = {c})) := by
  unfold program initial
  rw [DAGFiniteCompile.program_run]
  exact SharedPointOutputIndex.run_partial_at input c j

/-- Reverse the literal finite program to restore any finite register contents. -/
theorem reverse_run (state : Fin 509194 → ZMod 2) :
    Circuit.run program.reverse (Circuit.run program state) = state :=
  DAGFiniteCompile.program_reverse_run circuit.nodes outputRefs valid outputRefs_bounds
    509194 capacity_bound state

theorem output_injective : Function.Injective (fun p : Fin 50 × Fin 1176 => output p.1 p.2) := by
  intro p q he
  have hi : SharedPointOutputIndex.index p.1 p.2 = SharedPointOutputIndex.index q.1 q.2 := by
    by_contra hne
    exact SharedPointExecution.output_slots_distinct _ _
      (SharedPointOutputIndex.index_bound p.1 p.2) (SharedPointOutputIndex.index_bound q.1 q.2)
      hne (congrArg Fin.val he)
  exact Prod.ext ((SharedPointOutputIndex.index_eq_iff _ _ _ _).mp hi).1
    ((SharedPointOutputIndex.index_eq_iff _ _ _ _).mp hi).2

end IntegerMultBounds.Networks.Shared50Finite
