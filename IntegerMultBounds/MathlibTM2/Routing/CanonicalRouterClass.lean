module

public import IntegerMultBounds.MathlibTM2.Routing.CommonBankDirectional

/-! The canonical directional targets retain their local edge orientation after
physical placement. Three such directional shears recover one matching class. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
/-- Compose a family of three rank permutations without exposing their implementations. -/
def matchingRankSchedule {m : ℕ} (π : Fin 3 → Equiv.Perm (Fin m)) : Equiv.Perm (Fin m) :=
  ((π 2).trans (π 1)).trans (π 0)

theorem matchingRankSchedule_bits {m n : ℕ} (π : Fin 3 → Equiv.Perm (Fin m))
    (c : Fin 3 → Fin n → Fin n) (mate : Fin n → Fin n)
    (hc : ∀ q, c 2 (c 1 (c 0 q)) = mate q)
    (hb : ∀ k i q, (π k i).val.testBit q.val = i.val.testBit (c k q).val)
    (i : Fin m) (q : Fin n) :
    (matchingRankSchedule π i).val.testBit q.val = i.val.testBit (mate q).val := by
  change (π 0 (π 1 (π 2 i))).val.testBit q.val = _
  rw [hb, hb, hb, hc]

theorem matchingRankSchedule_row {m n : ℕ} (π : Fin 3 → Equiv.Perm (Fin m))
    (hr : ∀ k i, (π k i).val / 2 ^ n = i.val / 2 ^ n) (i : Fin m) :
    (matchingRankSchedule π i).val / 2 ^ n = i.val / 2 ^ n := by
  change (π 0 (π 1 (π 2 i))).val / 2 ^ n = _
  rw [hr, hr, hr]

variable (n : ℕ) (hn : canonicalRouterStride n ≤ n) (mate : Fin n → Fin n)
    (hinv : Function.Involutive mate) (k : Fin 3)

local notation "cls" => matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
  (routingReservoir_fit n (canonicalRouterGap n) hn)) mate k

def canonicalRouterClassTargets (reverse : Bool) : Finset (Fin n) :=
  (matchingDirectionTargets (canonicalRouterLocalMatching n hn k mate hinv) reverse).image
    (canonicalRouterMiddleEmbedding n hn k)

theorem canonicalRouterClassTargets_right :
    canonicalRouterClassTargets n hn mate hinv k true =
      (canonicalRouterClassTargets n hn mate hinv k false).image cls := by
  simp only [canonicalRouterClassTargets, matchingDirectionTargets, ite_true, Bool.false_eq_true,
    ite_false, Finset.image_image]
  congr 1
  funext q
  exact canonicalRouterMiddleEmbedding_source n hn k mate hinv q

/-- The exact physical target sets of the canonical executed directions give
one class matching in the false/true/false three-shear order. -/
theorem canonicalRouterClass_shears (x : Fin n → Bool) :
    shear (canonicalRouterClassTargets n hn mate hinv k false) cls
      (shear (canonicalRouterClassTargets n hn mate hinv k true) cls
        (shear (canonicalRouterClassTargets n hn mate hinv k false) cls x)) =
      fun q => x (cls q) := by
  rw [canonicalRouterClassTargets_right n hn mate hinv k]
  change matchingShears cls (canonicalRouterClassTargets n hn mate hinv k false) x = _
  have hf : canonicalRouterMiddleEmbedding n hn k =
      fun q => reservoirPlacement n (routingReservoirWidth n (canonicalRouterGap n))
        (routingReservoir_fit n (canonicalRouterGap n) hn)
        (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
        (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k
        (middleCoordinate (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
          (routerTargetWidth n (canonicalRouterStride n) (canonicalRouterGap n))
          (reservoirMiddle_fit n (routingReservoirWidth n (canonicalRouterGap n))
            (routingReservoir_fit n (canonicalRouterGap n) hn)
            (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
            (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))) q) := by
    funext q
    rfl
  simp only [canonicalRouterClassTargets, matchingDirectionTargets, Bool.false_eq_true, ite_false]
  erw [hf]
  exact reservoirClassLocalMatching_shears n (routingReservoirWidth n (canonicalRouterGap n))
    (routingReservoir_fit n (canonicalRouterGap n) hn)
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate hinv x


section Rank
variable {Q K : ℕ} (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)

local notation "direction" reverse => canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k reverse
  hQ hA l hl hlen (List.finRange (canonicalRouterStride n))

def canonicalRouterClassPerm : Equiv.Perm (Fin (R * 2 ^ n)) :=
  ((direction false).trans (direction true)).trans (direction false)

/-- The three actual directional rank permutations implement the physical
class matching on every record address. -/
theorem canonicalRouterClassPerm_bits (i : Fin (R * 2 ^ n)) :
    (fun q : Fin n => (canonicalRouterClassPerm n hn mate hinv k R B hR hB hQ hA l hl hlen i).val.testBit q.val) =
      fun q => i.val.testBit (cls q).val := by
  have h1 := canonicalRouterDirectionalPerm_bits n hn R B hR hB mate hinv k false hQ hA l hl hlen i
  have h2 := canonicalRouterDirectionalPerm_bits n hn R B hR hB mate hinv k true hQ hA l hl hlen
    ((direction false) i)
  have h3 := canonicalRouterDirectionalPerm_bits n hn R B hR hB mate hinv k false hQ hA l hl hlen
    ((direction true) ((direction false) i))
  rw [h2, h1] at h3
  exact h3.trans (canonicalRouterClass_shears n hn mate hinv k _)


theorem canonicalRouterClassPerm_row (i : Fin (R * 2 ^ n)) :
    (canonicalRouterClassPerm n hn mate hinv k R B hR hB hQ hA l hl hlen i).val / 2 ^ n =
      i.val / 2 ^ n := by
  change ((direction false) ((direction true) ((direction false) i))).val / 2 ^ n = _
  rw [canonicalRouterDirectionalPerm_row, canonicalRouterDirectionalPerm_row, canonicalRouterDirectionalPerm_row]

def canonicalRouterMatchingPerm : Equiv.Perm (Fin (R * 2 ^ n)) :=
  matchingRankSchedule (fun k => canonicalRouterClassPerm n hn mate hinv k R B hR hB hQ hA l hl hlen)

theorem canonicalRouterMatchingPerm_bits (i : Fin (R * 2 ^ n)) (q : Fin n) :
    (canonicalRouterMatchingPerm n hn mate hinv R B hR hB hQ hA l hl hlen i).val.testBit q.val =
      i.val.testBit (mate q).val :=
  matchingRankSchedule_bits
    (fun k => canonicalRouterClassPerm n hn mate hinv k R B hR hB hQ hA l hl hlen)
    (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
      (routingReservoir_fit n (canonicalRouterGap n) hn)) mate) mate
    (matchingClass_comp _ mate hinv)
    (fun k i q => congrFun (canonicalRouterClassPerm_bits n hn mate hinv k R B hR hB hQ hA l hl hlen i) q) i q

theorem canonicalRouterMatchingPerm_row (i : Fin (R * 2 ^ n)) :
    (canonicalRouterMatchingPerm n hn mate hinv R B hR hB hQ hA l hl hlen i).val / 2 ^ n =
      i.val / 2 ^ n :=
  matchingRankSchedule_row
    (fun k => canonicalRouterClassPerm n hn mate hinv k R B hR hB hQ hA l hl hlen)
    (fun k i => canonicalRouterClassPerm_row n hn mate hinv k R B hR hB hQ hA l hl hlen i) i

end Rank

end
end IntegerMultBounds.MathlibTM2.Routing
