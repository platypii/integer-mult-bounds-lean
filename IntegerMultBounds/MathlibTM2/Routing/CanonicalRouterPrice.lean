module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterMetadata
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalInputPrice

/-! Concrete canonical routing prices are fixed by dimensions and matching
metadata, independently of live record payload and order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3) (reverse : Bool)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l l' : List (List (Fin (prime + K + 4))))
    (hl : l.length = R * 2 ^ n) (hl' : l'.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)
    (hlen' : ∀ row ∈ l', row.length = B ∧ ∀ x ∈ row, x.val < 8)

local notation "input" => canonicalRouterInput n hn R B hR hB mate hinv k reverse hQ hA l hl hlen
local notation "input'" => canonicalRouterInput n hn R B hR hB mate hinv k reverse hQ hA l' hl' hlen'
local notation "str" => inactiveClassifierPlacementEmbed (t₀ := 6) (classifierCore (inactiveConfigurationCore repairHost.src))

theorem canonicalRouterInput_price_records_independent (r : Fin (canonicalRouterStride n)) :
    (input' r).price = (input r).price := by
  unfold canonicalRouterInput
  apply canonicalGeneratedInput_price_records_independent

theorem canonicalRouterOriginalPrice_records_independent (r : Fin (canonicalRouterStride n)) :
    originalMatchingPlacedPrice (input' r) (canonicalRouterCountWidth n r) n
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) =
    originalMatchingPlacedPrice (input r) (canonicalRouterCountWidth n r) n
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) := by
  unfold originalMatchingPlacedPrice matchingPlacedRepairPrice
  rw [canonicalRouterInput_price_records_independent n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen' r]
  dsimp only [canonicalRouterInput, canonicalGeneratedInput, GeneratedPlacedInput.coordinateWords]

theorem canonicalRouterStepPrice_records_independent (r : Fin (canonicalRouterStride n)) :
    originalMatchingStepPrice (input' r) (canonicalRouterCountWidth n r) n
      (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate canonicalRouterDelimiter =
    originalMatchingStepPrice (input r) (canonicalRouterCountWidth n r) n
      (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate canonicalRouterDelimiter := by
  unfold originalMatchingStepPrice
  rw [canonicalRouterOriginalPrice_records_independent n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen' r,
    canonicalRouterResidueFrame_records_independent n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen' r]
  simp only [framedCoreJobs, List.length_map]

theorem canonicalRouterBulkPrice_records_independent (stages : List (Fin (canonicalRouterStride n))) :
    commonBankBulkPrice n hn R B hR hB mate hinv k reverse hQ hA l' hl' hlen' stages =
      commonBankBulkPrice n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages := by
  unfold commonBankBulkPrice
  apply congrArg₂ (fun x y : ℝ => x + y)
  · apply congrArg (fun price : Fin (canonicalRouterStride n) → ℝ => delimitedSchedulePrice price stages)
    funext r
    exact canonicalRouterStepPrice_records_independent n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen' r
  · have hs := canonicalDirectionalBulkInput_records_independent n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen' stages
    dsimp only [canonicalDirectionalBulkInput] at hs
    rw [hs]

theorem canonicalDirectionalPrice_records_independent (L Lb : ℕ) (rowBits : List Bool)
    (stages : List (Fin (canonicalRouterStride n))) :
    canonicalDirectionalPrice n hn R B hR hB mate hinv k reverse hQ hA l' hl' hlen' L Lb rowBits stages =
      canonicalDirectionalPrice n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages := by
  unfold canonicalDirectionalPrice
  rw [canonicalRouterBulkPrice_records_independent n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen' stages,
    canonicalDirectionalFrame_records_independent n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen' L Lb rowBits stages]
  simp only [framedCoreJobs, List.length_map]

variable (L Lb : ℕ) (rowBits : List Bool)

theorem canonicalClassPrice_records_independent
    (data data' : CanonicalClassInput n hn R B hR hB mate hinv k hQ hA) :
    data.price L Lb rowBits = data'.price L Lb rowBits := by
  have hf (d : Fin 3) : data.directionPrice L Lb rowBits d = data'.directionPrice L Lb rowBits d :=
    canonicalDirectionalPrice_records_independent n hn R B hR hB mate hinv k (decide (d = 1)) hQ hA
      (data'.records d) (data.records d) (data'.count d) (data.count d) (data'.shape d) (data.shape d)
      L Lb rowBits (List.finRange (canonicalRouterStride n))
  unfold CanonicalClassInput.price
  rw [hf 0, hf 1, hf 2]

theorem canonicalMatchingPrice_records_independent :
    canonicalMatchingPrice n hn R B hR hB mate hinv hQ hA l' hl' hlen' L Lb rowBits =
      canonicalMatchingPrice n hn R B hR hB mate hinv hQ hA l hl hlen L Lb rowBits := by
  unfold canonicalMatchingPrice
  apply congrArg₂ (fun x y : ℝ => x + y)
  · apply congrArg₂ (fun x y : ℝ => x + y)
    · exact canonicalClassPrice_records_independent n hn R B hR hB mate hinv 2 hQ hA L Lb rowBits _ _
    · exact canonicalClassPrice_records_independent n hn R B hR hB mate hinv 1 hQ hA L Lb rowBits _ _
  · exact canonicalClassPrice_records_independent n hn R B hR hB mate hinv 0 hQ hA L Lb rowBits _ _

theorem canonicalPermutationPrice_records_independent (f : Equiv.Perm (Fin n)) :
    canonicalPermutationPrice n hn R B hR hB f hQ hA l' hl' hlen' L Lb rowBits =
      canonicalPermutationPrice n hn R B hR hB f hQ hA l hl hlen L Lb rowBits := by
  unfold canonicalPermutationPrice
  apply congrArg₂ (fun x y : ℝ => x + y)
  · exact canonicalMatchingPrice_records_independent n hn R B hR hB
      (fun q => f (permutationReflection f q)) (permutation_two_matchings f).2.1 hQ hA l l' hl hl' hlen hlen' L Lb rowBits
  · exact canonicalMatchingPrice_records_independent n hn R B hR hB
      (permutationReflection f) (permutation_two_matchings f).1 hQ hA
      (canonicalPermutationMiddle n hn R B hR hB f hQ hA l hl hlen)
      (canonicalPermutationMiddle n hn R B hR hB f hQ hA l' hl' hlen')
      (canonicalPermutationMiddle_count n hn R B hR hB f hQ hA l hl hlen)
      (canonicalPermutationMiddle_count n hn R B hR hB f hQ hA l' hl' hlen')
      (canonicalPermutationMiddle_shape n hn R B hR hB f hQ hA l hl hlen)
      (canonicalPermutationMiddle_shape n hn R B hR hB f hQ hA l' hl' hlen') L Lb rowBits

end
end IntegerMultBounds.MathlibTM2.Routing
