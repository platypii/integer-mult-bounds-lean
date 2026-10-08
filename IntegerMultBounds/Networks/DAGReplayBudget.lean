import IntegerMultBounds.Networks.DAGReplay
import IntegerMultBounds.Networks.DAGAllocatorBudget

/-! Count actual interned additions by their distinct supports. These bounds
connect replayed node lists to finite support-sharing certificates. -/

namespace IntegerMultBounds.Networks.DAGReplayBudget

open DisjointCircuit DAGReplay

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def isAddition (node : Node α) : Bool :=
  match node.kind with | .input _ => false | .add _ _ => true

omit [DecidableEq α] in
theorem isAddition_iff (node : Node α) :
    isAddition node = true ↔ ∃ l r, node.kind = .add l r := by
  cases hk : node.kind <;> simp [isAddition, hk]

/-- Only actual addition nodes contribute to this support budget. -/
def additionSupports (nodes : List (Node α)) : Finset (Finset α) :=
  ((nodes.filter isAddition).map Node.support).toFinset

theorem mem_additionSupports (nodes : List (Node α)) (support : Finset α) :
    support ∈ additionSupports nodes ↔ AdditionSupport nodes support := by
  simp only [additionSupports, List.mem_toFinset, List.mem_map, List.mem_filter,
    isAddition_iff, AdditionSupport]
  aesop

/-- Interning makes every counted addition occupy exactly one support. -/
theorem additionSupports_card (nodes : List (Node α)) (hn : (nodes.map Node.support).Nodup) :
    (additionSupports nodes).card = DAGAllocator.additionCount nodes := by
  have hf := hn.sublist (List.filter_sublist.map Node.support :
    ((nodes.filter isAddition).map Node.support).Sublist _)
  rw [additionSupports, List.toFinset_card_of_nodup hf, List.length_map,
    ← List.countP_eq_length_filter]
  rfl

theorem additions_le_card (nodes : List (Node α)) (budget : Finset (Finset α))
    (hn : (nodes.map Node.support).Nodup) (hs : additionSupports nodes ⊆ budget) :
    DAGAllocator.additionCount nodes ≤ budget.card := by
  rw [← additionSupports_card nodes hn]
  exact Finset.card_le_card hs

/-- A replay introduces no support outside the exact old/new support union. -/
theorem replay_supports_subset (rename : α ↪ β) (target : List (Node β))
    (source : List (Node α)) :
    additionSupports (replay rename target source).1 ⊆
      additionSupports target ∪ (additionSupports source).image (Finset.map rename) := by
  intro support hs
  rcases replay_additionSupport rename target source support
    ((mem_additionSupports _ _).mp hs) with hold | ⟨localSupport, hlocal, he⟩
  · exact Finset.mem_union_left _ ((mem_additionSupports _ _).mpr hold)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨localSupport, (mem_additionSupports _ _).mpr hlocal, he⟩)

/-- The actual replayed circuit is bounded by the number of distinct supports,
so a duplicate certificate applies to its physical addition count. -/
theorem replay_additions_le (rename : α ↪ β) (target : List (Node β))
    (source : List (Node α)) (hn : (target.map Node.support).Nodup) :
    DAGAllocator.additionCount (replay rename target source).1 ≤
      (additionSupports target ∪ (additionSupports source).image (Finset.map rename)).card :=
  additions_le_card _ _ (replay_nodup rename target source hn)
    (replay_supports_subset rename target source)

end IntegerMultBounds.Networks.DAGReplayBudget
