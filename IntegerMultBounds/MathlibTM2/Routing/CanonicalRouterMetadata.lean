module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalInputStream
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDirectionalExec

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

end
end IntegerMultBounds.MathlibTM2.Routing
