import IntegerMultBounds.Networks.DAGAllocatorCount

/-! Pruning can only improve the actual allocator's role budget. This lets a
fully checked, possibly unpruned certificate bound the compiled role count. -/

namespace IntegerMultBounds.Networks.DAGAllocator

open DisjointCircuit

/-- Count actual addition records in the concrete node list. -/
def additionCount {ι : Type*} (nodes : List (Node ι)) : ℕ :=
  nodes.countP (fun node => match node.kind with | .input _ => false | .add _ _ => true)

theorem marked_additions_le {ι : Type*} (nodes : List (Node ι)) (active : Finset ℕ) (offset : ℕ) :
    DisjointPruning.additionCountFrom offset active nodes ≤ additionCount nodes := by
  induction nodes generalizing offset with
  | nil => simp [DisjointPruning.additionCountFrom, additionCount]
  | cons node nodes ih =>
    have hh := ih (offset+1)
    cases node with
    | mk kind support =>
      cases kind <;> simp only [DisjointPruning.additionCountFrom, additionCount, List.countP_cons] at hh ⊢
      all_goals split_ifs <;> omega

/-- A checked certificate's total addition count bounds the role count of
its literal pruned compiler, even when the certificate retains dead nodes. -/
theorem compile_roles_le {ι : Type*} [DecidableEq ι] (nodes : List (Node ι))
    (outputs : List ℕ) (hv : Valid nodes) (ho : ∀ i ∈ outputs, i < nodes.length) :
    (compile nodes outputs).state.next ≤ additionCount nodes + outputs.length := by
  rw [compile_roles nodes outputs hv ho]
  exact Nat.add_le_add_right (marked_additions_le nodes _ 0) _

end IntegerMultBounds.Networks.DAGAllocator
