module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalMatchingRestore
public import IntegerMultBounds.MathlibTM2.Routing.PermutationMatchings

/-! The two explicit cycle reflections lift to the actual matching rank
permutations, including the changed records between matching calls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

def rankPairPerm {m : ℕ} (π σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin m) := π.trans σ

private theorem rankPair_bits {m n : ℕ} (π σ : Equiv.Perm (Fin m))
    (s t u : Fin n → Fin n) (hc : ∀ q, s (t q) = u q)
    (hπ : ∀ i q, (π i).val.testBit q.val = i.val.testBit (s q).val)
    (hσ : ∀ i q, (σ i).val.testBit q.val = i.val.testBit (t q).val)
    (i : Fin m) (q : Fin n) :
    (rankPairPerm π σ i).val.testBit q.val = i.val.testBit (u q).val :=
  (hσ (π i) q).trans ((hπ i (t q)).trans (congrArg (fun j : Fin n => i.val.testBit j.val) (hc q)))

private theorem rankPair_row {m n : ℕ} (π σ : Equiv.Perm (Fin m))
    (hπ : ∀ i, (π i).val / 2 ^ n = i.val / 2 ^ n)
    (hσ : ∀ i, (σ i).val / 2 ^ n = i.val / 2 ^ n) (i : Fin m) :
    (rankPairPerm π σ i).val / 2 ^ n = i.val / 2 ^ n := (hσ (π i)).trans (hπ i)

variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (f : Equiv.Perm (Fin n))
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)

attribute [local irreducible] canonicalRouterMatchingPerm canonicalRouterClassPerm canonicalRouterDirectionalPerm

local notation "a" => permutationReflection f
local notation "b" => fun q => f (permutationReflection f q)
local notation "ha" => And.left (permutation_two_matchings f)
local notation "hb" => And.left (And.right (permutation_two_matchings f))
local notation "π" => canonicalRouterMatchingPerm n hn b hb R B hR hB hQ hA l hl hlen

def canonicalPermutationMiddle : List (List (Fin (prime + K + 4))) := moveRecs π l

local notation "middle" => canonicalPermutationMiddle n hn R B hR hB f hQ hA l hl hlen

theorem canonicalPermutationMiddle_count : (middle).length = R * 2 ^ n := length_moveRecs _ _

theorem canonicalPermutationMiddle_shape :
    ∀ row ∈ middle, row.length = B ∧ ∀ x ∈ row, x.val < 8 :=
  fun row hr => hlen row (mem_moveRecs π hl hr)

local notation "middleCount" => canonicalPermutationMiddle_count n hn R B hR hB f hQ hA l hl hlen
local notation "middleShape" => canonicalPermutationMiddle_shape n hn R B hR hB f hQ hA l hl hlen
local notation "σ" => canonicalRouterMatchingPerm n hn a ha R B hR hB hQ hA middle middleCount middleShape

def canonicalPermutationRank : Equiv.Perm (Fin (R * 2 ^ n)) := rankPairPerm π σ

theorem canonicalPermutationRank_bits (i : Fin (R * 2 ^ n)) (q : Fin n) :
    (canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen i).val.testBit q.val =
      i.val.testBit (f q).val := by
  unfold canonicalPermutationRank
  have hπ := canonicalRouterMatchingPerm_bits n hn b hb R B hR hB hQ hA l hl hlen
  have hσ := canonicalRouterMatchingPerm_bits n hn a ha R B hR hB hQ hA middle middleCount middleShape
  exact rankPair_bits (m := R * 2 ^ n) (n := n) π σ b a f ((permutation_two_matchings f).2.2) hπ hσ i q

theorem canonicalPermutationRank_row (i : Fin (R * 2 ^ n)) :
    (canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen i).val / 2 ^ n = i.val / 2 ^ n := by
  unfold canonicalPermutationRank
  have hπ := canonicalRouterMatchingPerm_row n hn b hb R B hR hB hQ hA l hl hlen
  have hσ := canonicalRouterMatchingPerm_row n hn a ha R B hR hB hQ hA middle middleCount middleShape
  exact rankPair_row (m := R * 2 ^ n) (n := n) π σ hπ hσ i

end
end IntegerMultBounds.MathlibTM2.Routing
