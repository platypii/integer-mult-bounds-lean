import IntegerMultBounds.Machine.Shared50RecursivePieceExecution
import IntegerMultBounds.Machine.Shared50RecursiveDepth
import IntegerMultBounds.Machine.Shared50RecursiveNodeBoundary

/-! Charged coefficients and a natural-valued budget for the actual recursive
machine. Each child receives logical parent volume/W; parked ancestor storage
never enters the recursive argument. Execution must establish this budget. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveBudget
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50TapeGlobal (roleCount)
open RecursiveChildCallSetup (fields words)
attribute [local irreducible] Shared50PieceSchedule.pieces Shared50RecursiveCallLayout.parked

def base (k : ℕ) := RecursiveDigitRoleBank.coefficient+134+k

def node (k : ℕ) :=
  Shared50RecursiveNodeBoundary.entryConstant+Shared50RecursiveNodeBoundary.exitConstant+
    (Shared50PieceSchedule.pieces.map (Shared50RecursivePieceExecution.overhead k)).sum+135+k

/-- The target budget includes all actual nonrecursive work and one same-volume
recursive budget for each literal call. Correctness is proved separately. -/
def budget (k : ℕ) : ℕ → ℕ → ℕ
  | 0, V => base k*V
  | depth+1, V => node k*V+Shared50Parameters.s*budget k depth (V/roleCount)

/-- Bound occupied-header cleanup and parent-frame restoration using only the
word lengths charged to the current logical child volume. -/
theorem return_cost_bound (V : ℕ) (hV : 0 < V) (old current : Fin 6 → List Bool)
    (ho : ∀ i, (old i).length ≤ 2*V) (hc : ∀ i, (current i).length ≤ 2*V) :
    RecursiveChildCallReturn.cost old current ≤ 127*V := by
  have hpop := BinaryDescriptorFrames.six_field_cost fields (by simp [fields]) (words old)
    (2*V) (by
      intro op hop
      obtain ⟨z,rfl⟩ := List.mem_ofFn.mp hop
      rw [RecursiveChildCallSetup.words_header]
      exact ho z)
  have hclear := BinaryDescriptorCleanupList.cost_le (BinaryDescriptorFrameRestore.slots fields) (words current)
    (2*V) (by
      intro z hz
      obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hop
      rw [RecursiveChildCallSetup.words_header]
      exact hc i)
  have hlen : (BinaryDescriptorFrameRestore.slots fields).length = 6 := by
    simp [BinaryDescriptorFrameRestore.slots,fields]
  rw [hlen] at hclear
  unfold RecursiveChildCallReturn.cost
  omega

end
end IntegerMultBounds.Machine.Shared50RecursiveBudget
