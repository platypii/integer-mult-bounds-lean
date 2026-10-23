module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalInputStream
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPermutationExec

/-! Canonical router metadata transport between arbitrary live record streams. -/

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

theorem canonicalRouterInput_bank_updateStream (r : Fin (canonicalRouterStride n)) :
    (input' r).M.R = Function.update (input r).M.R str l'.flatten := by
  unfold canonicalRouterInput
  apply canonicalGeneratedInput_bank_updateStream

theorem canonicalRouterInput_originalMatchingBank (r : Fin (canonicalRouterStride n)) :
    originalMatchingPlacedInputBank (input' r) (canonicalRouterCountWidth n r) n
      (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate =
      Function.update (originalMatchingPlacedInputBank (input r) (canonicalRouterCountWidth n r) n
        (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
        (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
        (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate)
        (originalMatchingScheduleStream 6) l'.flatten := by
  unfold originalMatchingPlacedInputBank matchingPlacedInputBank
  rw [canonicalRouterInput_bank_updateStream n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen' r]
  have hc : (input' r).coordinateRegister = (input r).coordinateRegister := by
    dsimp only [GeneratedPlacedInput.coordinateRegister, canonicalRouterInput, canonicalGeneratedInput]
  rw [hc]
  have hcomm := Function.update_comm (β := fun _ : Fin (inactiveClassifierPlacementT 6) => List (Fin (prime + K + 4)))
    (input r).coordinateRegister_ne_stream.symm l'.flatten [] (input r).M.R
  rw [hcomm]
  dsimp only [matchingInitialBank]
  rw [matchingProductionBank_updateCore]
  apply originalMatchingInputBank_updateRepair
  exact matchingCoreEmbed_extract _ _ 5

theorem canonicalRouterResidueFrame_records_independent (r : Fin (canonicalRouterStride n)) :
    originalMatchingFrame (input' r) (canonicalRouterCountWidth n r) n
      (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate canonicalRouterDelimiter =
    originalMatchingFrame (input r) (canonicalRouterCountWidth n r) n
      (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate canonicalRouterDelimiter := by
  unfold originalMatchingFrame
  rw [canonicalRouterInput_originalMatchingBank n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen' r]
  exact framedCoreFrames_updateStream (N := originalMatchingScheduleT 6)
    (framedCoreEmbed (originalMatchingScheduleT 6)) (originalMatchingScheduleStream 6) canonicalRouterDelimiter _ l'.flatten

theorem canonicalDirectionalBulkInput_records_independent (stages : List (Fin (canonicalRouterStride n))) :
    canonicalDirectionalBulkInput n hn R B hR hB mate hinv k reverse hQ hA l' hl' hlen' stages =
      canonicalDirectionalBulkInput n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages := by
  unfold canonicalDirectionalBulkInput
  apply congrArg (fun frame : Fin (canonicalRouterStride n) → List (Fin (prime + K + 4)) =>
    delimitedScheduleInput frame stages)
  funext r
  exact canonicalRouterResidueFrame_records_independent n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen' r

variable (L Lb : ℕ) (rowBits : List Bool) (stages : List (Fin (canonicalRouterStride n)))
local notation "bank" => canonicalDirectionalBank n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages
local notation "bank'" => canonicalDirectionalBank n hn R B hR hB mate hinv k reverse hQ hA l' hl' hlen' L Lb rowBits stages
local notation "bulk" => Function.update (fun _ : Fin canonicalRouterBulkT => ([] : List (Fin (prime + K + 4))))
  (originalMatchingScheduleStream 6) l.flatten
local notation "terminal" => canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
  (canonicalTerminalAux 0) l.flatten (elementaryCoordinateFrames L
    (canonicalRouterTerminalCoordinates n hn mate hinv k reverse)) n L Lb B rowBits
local notation "coreStream" => canonicalRouterBulkEmbed (originalMatchingScheduleStream 6)

theorem canonicalDirectionalBank_records_update :
    bank' = Function.update bank canonicalDirectionalStream l'.flatten := by
  have hc := canonicalRouterCommonBank_updateStream bulk terminal l'.flatten
  simp only [Function.update_idem, canonicalTerminalRoutingBank_updateStream] at hc
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · change bank' (framedCoreEmbed canonicalRouterCommonT i) =
      Function.update bank (framedCoreEmbed canonicalRouterCommonT coreStream) l'.flatten (framedCoreEmbed canonicalRouterCommonT i)
    rw [canonicalDirectionalBank_core, hc]
    by_cases hi : i = coreStream
    · subst i
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hi, Function.update_of_ne ((framedCoreEmbed_injective canonicalRouterCommonT).ne hi),
        canonicalDirectionalBank_core]
  · change bank' (framedCoreAux canonicalRouterCommonT i) =
      Function.update bank (framedCoreEmbed canonicalRouterCommonT coreStream) l'.flatten (framedCoreAux canonicalRouterCommonT i)
    rw [Function.update_of_ne (framedCoreEmbed_aux canonicalRouterCommonT coreStream i).symm,
      canonicalDirectionalBank_aux, canonicalDirectionalBank_aux,
      canonicalDirectionalBulkInput_records_independent n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen' stages]

theorem canonicalDirectionalFrame_records_independent :
    canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l' hl' hlen' L Lb rowBits stages =
      canonicalDirectionalFrame n hn R B hR hB mate hinv k reverse hQ hA l hl hlen L Lb rowBits stages := by
  unfold canonicalDirectionalFrame
  rw [canonicalDirectionalBank_records_update n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen' L Lb rowBits stages]
  exact framedCoreFrames_updateStream (N := canonicalRouterCommonT + 3)
    (framedCoreEmbed (canonicalRouterCommonT + 3)) canonicalDirectionalStream canonicalDirectionalOuterDelimiter _ l'.flatten

theorem canonicalClassFrame_records_independent
    (data data' : CanonicalClassInput n hn R B hR hB mate hinv k hQ hA) :
    data.frame L Lb rowBits = data'.frame L Lb rowBits := by
  have hf (d : Fin 3) : data.directionFrame L Lb rowBits d = data'.directionFrame L Lb rowBits d :=
    canonicalDirectionalFrame_records_independent n hn R B hR hB mate hinv k (decide (d = 1)) hQ hA
      (data'.records d) (data.records d) (data'.count d) (data.count d) (data'.shape d) (data.shape d)
      L Lb rowBits (List.finRange (canonicalRouterStride n))
  unfold CanonicalClassInput.frame
  rw [hf 0, hf 1, hf 2]

theorem canonicalMatchingFrame_records_independent :
    canonicalMatchingFrame n hn R B hR hB mate hinv hQ hA l' hl' hlen' L Lb rowBits =
      canonicalMatchingFrame n hn R B hR hB mate hinv hQ hA l hl hlen L Lb rowBits := by
  unfold canonicalMatchingFrame
  apply congrArg₂ List.append
  · exact canonicalClassFrame_records_independent n hn R B hR hB mate hinv 2 hQ hA L Lb rowBits _ _
  · apply congrArg₂ List.append
    · exact canonicalClassFrame_records_independent n hn R B hR hB mate hinv 1 hQ hA L Lb rowBits _ _
    · exact canonicalClassFrame_records_independent n hn R B hR hB mate hinv 0 hQ hA L Lb rowBits _ _

theorem canonicalPermutationFrame_records_independent (f : Equiv.Perm (Fin n)) :
    canonicalPermutationFrame n hn R B hR hB f hQ hA l' hl' hlen' L Lb rowBits =
      canonicalPermutationFrame n hn R B hR hB f hQ hA l hl hlen L Lb rowBits := by
  unfold canonicalPermutationFrame
  apply congrArg₂ List.append
  · exact canonicalMatchingFrame_records_independent n hn R B hR hB
      (fun q => f (permutationReflection f q)) (permutation_two_matchings f).2.1 hQ hA l l' hl hl' hlen hlen' L Lb rowBits
  · exact canonicalMatchingFrame_records_independent n hn R B hR hB
      (permutationReflection f) (permutation_two_matchings f).1 hQ hA
      (canonicalPermutationMiddle n hn R B hR hB f hQ hA l hl hlen)
      (canonicalPermutationMiddle n hn R B hR hB f hQ hA l' hl' hlen')
      (canonicalPermutationMiddle_count n hn R B hR hB f hQ hA l hl hlen)
      (canonicalPermutationMiddle_count n hn R B hR hB f hQ hA l' hl' hlen')
      (canonicalPermutationMiddle_shape n hn R B hR hB f hQ hA l hl hlen)
      (canonicalPermutationMiddle_shape n hn R B hR hB f hQ hA l' hl' hlen') L Lb rowBits

end
end IntegerMultBounds.MathlibTM2.Routing
