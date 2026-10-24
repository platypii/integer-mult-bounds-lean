module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRowCall
public import IntegerMultBounds.MathlibTM2.Routing.CoordinateRowRank

/-! Instantiate row locality with the actual canonical coordinate ranks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ}

private theorem castRankPerm_testBit {M N : ℕ} (h : M = N)
    (π : Equiv.Perm (Fin M)) (i : Fin N) (q : ℕ) :
    (castRankPerm h π i).val.testBit q = (π (Fin.cast h.symm i)).val.testBit q := by
  cases h
  rfl

def canonicalLocalRank (n : ℕ) (hn : canonicalRouterStride n ≤ n) (B : ℕ) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (2 ^ n)) :=
  castRankPerm (Nat.one_mul (2 ^ n))
    (canonicalPermutationRank n hn 1 B (by decide) hB f hQ hA
      (canonicalRouterZeroRecords n 1 B) (canonicalRouterZeroRecords_count n 1 B)
      (canonicalRouterZeroRecords_shape n 1 B))

theorem canonicalLocalRank_bits (n : ℕ) (hn : canonicalRouterStride n ≤ n) (B : ℕ) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n)) (i : Fin (2 ^ n)) (q : Fin n) :
    (canonicalLocalRank n hn B hB hQ hA f i).val.testBit q.val = i.val.testBit (f q).val := by
  exact (castRankPerm_testBit (Nat.one_mul (2 ^ n)) _ i q.val).trans
    (canonicalPermutationRank_bits n hn 1 B (by decide) hB f hQ hA
    (canonicalRouterZeroRecords n 1 B) (canonicalRouterZeroRecords_count n 1 B)
    (canonicalRouterZeroRecords_shape n 1 B) _ q)

private theorem moveRecs_ofFn {α : Type*} {M : ℕ} (π : Equiv.Perm (Fin M))
    (records : Fin M → List α) :
    moveRecs π (List.ofFn records) = List.ofFn (fun i => records (π.symm i)) := by
  simp [moveRecs, List.getD_eq_getElem?_getD]

theorem canonicalRowEffect_localRank
    (n : ℕ) (hn : canonicalRouterStride n ≤ n) (B : ℕ) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n))
    (l : List (List (Fin (prime + K + 4))))
    (hlen : ∀ row ∈ l, row.length = B) :
    canonicalRowEffect n hn B hB hQ hA f l.flatten =
      (moveRecs (canonicalLocalRank n hn B hB hQ hA f) l).flatten := by
  unfold canonicalRowEffect repairStreamEffect
  rw [← flatten_moveRecs _ l hlen]
  exact congrArg List.flatten (moveRecs_castRankPerm (Nat.one_mul (2 ^ n)) _ l).symm

/-- A structural row slice of a complete record rectangle. -/
def canonicalRowRecords {α : Type*} (n : ℕ) (l : List (List α)) (row : ℕ) : List (List α) :=
  List.ofFn fun i : Fin (2 ^ n) => l.getD (row * 2 ^ n + i.val) []

theorem canonicalRowRecords_reassemble {α : Type*} (n R : ℕ) (l : List (List α))
    (hl : l.length = R * 2 ^ n) :
    (List.ofFn fun row : Fin R => canonicalRowRecords n l row.val).flatten = l := by
  have h : (List.ofFn fun i : Fin (R * 2 ^ n) => l.getD i.val []) = l := by
    apply List.ext_getElem (by simp [hl])
    intro i hi hi'
    simp only [List.getElem_ofFn]
    rw [List.getD_eq_getElem l [] hi']
  rw [List.ofFn_mul] at h
  exact h

theorem canonicalRowRecords_stream {α : Type*} (n R : ℕ) (l : List (List α))
    (hl : l.length = R * 2 ^ n) :
    (List.ofFn fun row : Fin R => (canonicalRowRecords n l row.val).flatten).flatten = l.flatten := by
  change (List.ofFn (List.flatten ∘ fun row : Fin R => canonicalRowRecords n l row.val)).flatten = _
  rw [← List.map_ofFn, ← List.flatten_flatten, canonicalRowRecords_reassemble n R l hl]

theorem canonicalRowRecords_shape {α : Type*} (n R B : ℕ) (l : List (List α))
    (hl : l.length = R * 2 ^ n) (P : α → Prop)
    (hlen : ∀ record ∈ l, record.length = B ∧ ∀ x ∈ record, P x) (row : Fin R) :
    (canonicalRowRecords n l row.val).length = 1 * 2 ^ n ∧
      ∀ record ∈ canonicalRowRecords n l row.val, record.length = B ∧ ∀ x ∈ record, P x := by
  refine ⟨by simp [canonicalRowRecords], ?_⟩
  intro record hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  have hi : row.val * 2 ^ n + i.val < l.length := by
    rw [hl]
    have hm := Nat.mul_le_mul_right (2 ^ n) (Nat.succ_le_of_lt row.isLt)
    simp only [Nat.succ_mul] at hm
    omega
  rw [List.getD_eq_getElem l [] hi]
  exact hlen _ (List.getElem_mem hi)

theorem moveRecs_canonical_rows
    (n : ℕ) (hn : canonicalRouterStride n ≤ n) (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n))
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8) :
    moveRecs (canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen) l =
      (List.ofFn fun row : Fin R => List.ofFn fun i : Fin (2 ^ n) =>
        l.getD (row.val * 2 ^ n + ((canonicalLocalRank n hn B hB hQ hA f).symm i).val) []).flatten := by
  apply moveRecs_coordinate_rows R n _ _ f
  · exact canonicalPermutationRank_bits n hn R B hR hB f hQ hA l hl hlen
  · exact canonicalLocalRank_bits n hn B hB hQ hA f
  · exact canonicalPermutationRank_row n hn R B hR hB f hQ hA l hl hlen

/-- The row driver's concatenated effects equal the actual global router endpoint. -/
theorem canonicalRowEffects_global
    (n : ℕ) (hn : canonicalRouterStride n ≤ n) (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (f : Equiv.Perm (Fin n))
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ record ∈ l, record.length = B ∧ ∀ x ∈ record, x.val < 8) :
    (List.ofFn fun row : Fin R => canonicalRowEffect n hn B hB hQ hA f
      (canonicalRowRecords n l row.val).flatten).flatten =
      (moveRecs (canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen) l).flatten := by
  rw [moveRecs_canonical_rows n hn R B hR hB hQ hA f l hl hlen,
    List.flatten_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  have hshape := canonicalRowRecords_shape n R B l hl (fun x => x.val < 8) hlen row
  rw [canonicalRowEffect_localRank n hn B hB hQ hA f _
    (fun record hr => (hshape.2 record hr).1)]
  unfold canonicalRowRecords
  rw [moveRecs_ofFn]
  rfl

end
end IntegerMultBounds.MathlibTM2.Routing
