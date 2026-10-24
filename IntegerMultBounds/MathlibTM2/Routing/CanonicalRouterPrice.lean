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

def canonicalRouterGeneratedCostBound (n R B width : ℕ) : ℝ :=
  let rb := canonicalScalarWidth R
  (canonicalRouterGeneratedOverhead n R B width : ℕ) +
    (selectiveUniformKeyPassCost n rb (R * 2 ^ n) B : ℕ) +
    (12 * (selectiveUniformRotationCost n (R * 2 ^ n) (n + rb + B) : ℕ) +
      12 * selectiveUniformSwapCost repairT (R * 2 ^ n) (n + rb + B)
        (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
        (swapT 6 * (width + 1)) + 1) +
    repairUniformDensityScanCost n rb R B (n + 1 : ℕ)

theorem canonicalRouterInput_generatedCost_le (r : Fin (canonicalRouterStride n)) (width : ℕ) :
    (input r).generatedCostBound n width ≤ canonicalRouterGeneratedCostBound n R B width := by
  have ho := canonicalRouterGeneratedOverhead_le n hn r R B hR hB width
  exact add_le_add (add_le_add (add_le_add (Nat.cast_le.mpr ho) (le_refl _)) (le_refl _)) (le_refl _)

def canonicalRouterPlacementCostBound (n R B : ℕ) : ℝ :=
  let T := inactiveClassifierPlacementT 6
  let H := routingReservoirWidth n (canonicalRouterGap n)
  let w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
  let Lc := canonicalScalarWidth n
  let L := canonicalScalarWidth B
  (3 * swapConst * (T + 12 * swapT 6 + 5 : ℕ) * (R * 2 ^ n * B : ℕ)) *
    (((max 1 (3 * H) : ℕ) : ℝ) ^ Parameters.tau + 2 * ((max 1 w : ℕ) : ℝ) ^ Parameters.tau) +
    3 * (generatedExchangeUniformOverhead 6 T n R B L (R.log2 + 1) Lc 0 +
      (3 * (Lc * (4 * n + 31) + 2 * n + 26) + 10 * Lc + 12) + (2 * n + 2 * Lc + 9) : ℕ) + 1

theorem canonicalRouterInput_placementCost_le (r : Fin (canonicalRouterStride n)) :
    (input r).placementCostBound ≤ canonicalRouterPlacementCostBound n R B := by
  have hf := routerProfileFieldsLen n (canonicalRouterStride n) (canonicalRouterGap n) hn r
  have hrow := (canonicalRouterRecordWidths n hn r R B hR hB).2.2.2.2.2
  have ho := generatedExchangeUniformOverhead_mono 6 (inactiveClassifierPlacementT 6) n R B
    (le_refl (canonicalScalarWidth B)) hrow (le_refl (canonicalScalarWidth n)) (le_refl 0)
  dsimp only [GeneratedPlacedInput.placementCostBound, canonicalRouterInput, canonicalGeneratedInput,
    canonicalRouterArithmetic, canonicalStageArithmetic]
  rw [hf, routerProfileParameters_borrowed]
  have hc : (generatedExchangeUniformOverhead 6 (inactiveClassifierPlacementT 6) n R B
      (canonicalScalarWidth B) (GrowingCounterData.advance R []).length (canonicalScalarWidth n) 0 : ℝ) ≤
      (generatedExchangeUniformOverhead 6 (inactiveClassifierPlacementT 6) n R B
        (canonicalScalarWidth B) (R.log2 + 1) (canonicalScalarWidth n) 0 : ℕ) := Nat.cast_le.mpr ho
  dsimp only [canonicalRouterPlacementCostBound]
  simp only [Nat.cast_add] at hc ⊢
  linarith only [hc]

theorem canonicalRouterInput_price_le (r : Fin (canonicalRouterStride n)) :
    let width := n + canonicalScalarWidth R +
      canonicalScalarWidth (3 * (n + canonicalScalarWidth R + B)) + canonicalScalarWidth n + 1
    (input r).price ≤ 2 * (input r).placementCostBound + (input r).generatedCostBound n width := by
  unfold canonicalRouterInput
  apply canonicalGeneratedInput_price_le
  · exact routerProfileFieldsLen n (canonicalRouterStride n) (canonicalRouterGap n) hn r
  · exact (canonicalRouterSlots_le n hn r).1
  · exact (canonicalRouterSlots_le n hn r).2
  · exact canonicalRouterHeaders_length_le n hn r R B hR

def canonicalRouterStageCostBound (n R B : ℕ) : ℝ :=
  let width := n + canonicalScalarWidth R +
    canonicalScalarWidth (3 * (n + canonicalScalarWidth R + B)) + canonicalScalarWidth n + 1
  2 * canonicalRouterPlacementCostBound n R B + canonicalRouterGeneratedCostBound n R B width

theorem canonicalRouterInput_price_uniform (r : Fin (canonicalRouterStride n)) :
    (input r).price ≤ canonicalRouterStageCostBound n R B := by
  have hp := canonicalRouterInput_price_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r
  have hm := canonicalRouterInput_placementCost_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r
  have hg := canonicalRouterInput_generatedCost_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r
    (n + canonicalScalarWidth R + canonicalScalarWidth (3 * (n + canonicalScalarWidth R + B)) +
      canonicalScalarWidth n + 1)
  exact hp.trans (add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2)) hg)

theorem canonicalRouterInput_prices_sum_le (stages : List (Fin (canonicalRouterStride n))) :
    (stages.map (fun r => (input r).price)).sum ≤ stages.length * canonicalRouterStageCostBound n R B := by
  induction stages with
  | nil => simp
  | cons r stages ih =>
    have hp := canonicalRouterInput_price_uniform n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith only [hp, ih]

theorem canonicalRouterBulkPrice_uniform (stages : List (Fin (canonicalRouterStride n))) :
    commonBankBulkPrice n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages ≤
      stages.length * canonicalRouterStageCostBound n R B +
        (stages.length * (canonicalRouterStageSetupBudget n R B + 2 +
          2 * canonicalRouterUniformFrameWidth n R B) + 4 : ℕ) := by
  exact (commonBankBulkPrice_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages).trans
    (add_le_add (canonicalRouterInput_prices_sum_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages)
      (le_refl _))

def canonicalRouterDirectionalCostBound (n R B L Lb rowLength count : ℕ) : ℝ :=
  canonicalTerminalPrice n R B L Lb rowLength (131 * canonicalRouterGap n) +
    (count * canonicalRouterStageCostBound n R B +
      (count * (canonicalRouterStageSetupBudget n R B + 2 + 2 * canonicalRouterUniformFrameWidth n R B) + 4 : ℕ)) +
    (6 * canonicalDirectionalUniformFrameBudget n R B L Lb rowLength count +
      2 * (canonicalRouterCommonT + 3) + 2 : ℕ)

theorem canonicalRouterDirectionalCostBound_mono_rowLength (n R B L Lb count : ℕ)
    {rowLength rowLength' : ℕ} (hrow : rowLength ≤ rowLength') :
    canonicalRouterDirectionalCostBound n R B L Lb rowLength count ≤
      canonicalRouterDirectionalCostBound n R B L Lb rowLength' count := by
  unfold canonicalRouterDirectionalCostBound canonicalTerminalPrice canonicalDirectionalUniformFrameBudget
    elementaryCompileBase elementaryCompilerPrepareBound
  gcongr

theorem canonicalRouterDirectionalPrice_uniform (L Lb : ℕ) (rowBits : List Bool)
    (stages : List (Fin (canonicalRouterStride n))) :
    canonicalDirectionalPrice n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages ≤
      canonicalRouterDirectionalCostBound n R B L Lb rowBits.length stages.length := by
  have hp := canonicalDirectionalPrice_uniform_overhead n hn R B hR hB mate hinv k reverse hQ hA
    l hl hlen L Lb rowBits stages
  have hb := canonicalRouterBulkPrice_uniform n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages
  exact hp.trans (add_le_add (add_le_add (le_refl _) hb) (le_refl _))

theorem canonicalRouterClassPrice_uniform
    (classInput : CanonicalClassInput n hn R B hR hB mate hinv k hQ hA)
    (L Lb : ℕ) (rowBits : List Bool) :
    classInput.price L Lb rowBits ≤
      3 * canonicalRouterDirectionalCostBound n R B L Lb rowBits.length (canonicalRouterStride n) := by
  have hd (d : Fin 3) : classInput.directionPrice L Lb rowBits d ≤
      canonicalRouterDirectionalCostBound n R B L Lb rowBits.length (canonicalRouterStride n) := by
    simpa only [CanonicalClassInput.directionPrice, List.length_finRange] using
      canonicalRouterDirectionalPrice_uniform n hn R B hR hB mate hinv k (decide (d = 1)) hQ hA
        (classInput.records d) (classInput.count d) (classInput.shape d) L Lb rowBits
        (List.finRange (canonicalRouterStride n))
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  unfold CanonicalClassInput.price
  linarith only [h₀, h₁, h₂]

theorem canonicalRouterMatchingPrice_uniform (L Lb : ℕ) (rowBits : List Bool) :
    canonicalMatchingPrice n hn R B hR hB mate hinv hQ hA l hl hlen L Lb rowBits ≤
      9 * canonicalRouterDirectionalCostBound n R B L Lb rowBits.length (canonicalRouterStride n) := by
  have hc (d : Fin 3) := canonicalRouterClassPrice_uniform n hn R B hR hB mate hinv d hQ hA
    (canonicalMatchingInput n hn R B hR hB mate hinv hQ hA l hl hlen d) L Lb rowBits
  have h₀ := hc 0
  have h₁ := hc 1
  have h₂ := hc 2
  unfold canonicalMatchingPrice
  linarith only [h₀, h₁, h₂]

theorem canonicalRouterPermutationPrice_uniform (f : Equiv.Perm (Fin n)) (L Lb : ℕ) (rowBits : List Bool) :
    canonicalPermutationPrice n hn R B hR hB f hQ hA l hl hlen L Lb rowBits ≤
      18 * canonicalRouterDirectionalCostBound n R B L Lb rowBits.length (canonicalRouterStride n) := by
  have h₀ := canonicalRouterMatchingPrice_uniform n hn R B hR hB
    (fun q => f (permutationReflection f q)) (permutation_two_matchings f).2.1
    hQ hA l hl hlen L Lb rowBits
  have h₁ := canonicalRouterMatchingPrice_uniform n hn R B hR hB
    (permutationReflection f) (permutation_two_matchings f).1 hQ hA
    (canonicalPermutationMiddle n hn R B hR hB f hQ hA l hl hlen)
    (canonicalPermutationMiddle_count n hn R B hR hB f hQ hA l hl hlen)
    (canonicalPermutationMiddle_shape n hn R B hR hB f hQ hA l hl hlen) L Lb rowBits
  unfold canonicalPermutationPrice
  linarith only [h₀, h₁]

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
