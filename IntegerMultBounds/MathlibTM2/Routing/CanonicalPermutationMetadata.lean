module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterPrice

/-! A metadata frame defined from dimensions and the coordinate permutation,
with no live record payload in its interface. Construction is still pure data. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

def canonicalRouterZeroRecords {K : ℕ} (n R B : ℕ) : List (List (Fin (prime + K + 4))) :=
  List.replicate (R * 2 ^ n) (List.replicate B ⟨0, by omega⟩)

theorem canonicalRouterZeroRecords_count {K : ℕ} (n R B : ℕ) :
    (canonicalRouterZeroRecords (K := K) n R B).length = R * 2 ^ n := List.length_replicate

theorem canonicalRouterZeroRecords_shape {K : ℕ} (n R B : ℕ) :
    ∀ row ∈ canonicalRouterZeroRecords (K := K) n R B, row.length = B ∧ ∀ x ∈ row, x.val < 8 := by
  intro row hr
  have hrow := List.eq_of_mem_replicate hr
  subst row
  refine ⟨List.length_replicate, ?_⟩
  intro x hx
  have hzero := List.eq_of_mem_replicate hx
  subst x
  change (0 : ℕ) < 8
  decide

variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (f : Equiv.Perm (Fin n))
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (L Lb : ℕ) (rowBits : List Bool)

def canonicalPermutationMetadata : List (Fin (prime + K + 4)) :=
  canonicalPermutationFrame n hn R B hR hB f hQ hA
    (canonicalRouterZeroRecords n R B) (canonicalRouterZeroRecords_count n R B)
    (canonicalRouterZeroRecords_shape n R B) L Lb rowBits

theorem canonicalPermutationFrame_eq_metadata
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8) :
    canonicalPermutationFrame n hn R B hR hB f hQ hA l hl hlen L Lb rowBits =
      canonicalPermutationMetadata n hn R B hR hB f hQ hA L Lb rowBits :=
  canonicalPermutationFrame_records_independent n hn R B hR hB
    hQ hA (canonicalRouterZeroRecords n R B) l
    (canonicalRouterZeroRecords_count n R B) hl (canonicalRouterZeroRecords_shape n R B) hlen L Lb rowBits f

/-- Complete eighteen-direction price, including the final input rewind,
with no live record payload in the budget's parameters. -/
def canonicalPermutationBudget : ℝ :=
  canonicalPermutationPrice n hn R B hR hB f hQ hA
    (canonicalRouterZeroRecords n R B) (canonicalRouterZeroRecords_count n R B)
    (canonicalRouterZeroRecords_shape n R B) L Lb rowBits +
    (2 * (canonicalPermutationMetadata n hn R B hR hB f hQ hA L Lb rowBits).length + 2 : ℕ)

theorem canonicalPermutationCost_eq_budget
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8) :
    canonicalPermutationPrice n hn R B hR hB f hQ hA l hl hlen L Lb rowBits +
      (2 * (canonicalPermutationFrame n hn R B hR hB f hQ hA l hl hlen L Lb rowBits).length + 2 : ℕ) =
      canonicalPermutationBudget n hn R B hR hB f hQ hA L Lb rowBits := by
  rw [canonicalPermutationFrame_eq_metadata n hn R B hR hB f hQ hA L Lb rowBits l hl hlen,
    canonicalPermutationPrice_records_independent n hn R B hR hB hQ hA
      (canonicalRouterZeroRecords n R B) l (canonicalRouterZeroRecords_count n R B) hl
      (canonicalRouterZeroRecords_shape n R B) hlen L Lb rowBits f]
  rfl

end
end IntegerMultBounds.MathlibTM2.Routing
