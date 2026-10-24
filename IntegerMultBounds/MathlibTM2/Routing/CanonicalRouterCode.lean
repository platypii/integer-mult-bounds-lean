module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPermutationMetadata

/-! The concrete router code is independent of record payload and order.
Only live operands and the record stream carry changing input data. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
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

theorem canonicalRouterBulkCode_records_independent :
    commonBankBulkProgram n hn R B hR hB mate hinv k reverse hQ hA l' hl' hlen' =
      commonBankBulkProgram n hn R B hR hB mate hinv k reverse hQ hA l hl hlen := by
  dsimp only [commonBankBulkProgram, originalMatchingPlacedProgram, matchingGeneratedPlacedProgram,
    canonicalRouterInput, canonicalGeneratedInput, GeneratedPlacedInput.coordinateRegister]

/-- Bulk dimensions and matching data are operands, rather than program syntax. -/
theorem canonicalRouterBulkCode_geometry_independent
    (n' : ℕ) (hn' : canonicalRouterStride n' ≤ n')
    (R' B' : ℕ) (hR' : 0 < R') (hB' : 1 ≤ B')
    (mate' : Fin n' → Fin n') (hinv' : Function.Involutive mate')
    (records : List (List (Fin (prime + K + 4))))
    (count : records.length = R' * 2 ^ n')
    (shape : ∀ row ∈ records, row.length = B' ∧ ∀ x ∈ row, x.val < 8) :
    commonBankBulkProgram n' hn' R' B' hR' hB' mate' hinv' k reverse hQ hA records count shape =
      commonBankBulkProgram n hn R B hR hB mate hinv k reverse hQ hA l hl hlen := by
  rfl

theorem canonicalDirectionalCode_records_independent (Lb : ℕ) (rowBits : List Bool) :
    canonicalDirectionalProgram n hn R B hR hB mate hinv k reverse hQ hA l' hl' hlen' Lb rowBits =
      canonicalDirectionalProgram n hn R B hR hB mate hinv k reverse hQ hA l hl hlen Lb rowBits := by
  unfold canonicalDirectionalProgram canonicalDirectionalCore
  rw [canonicalRouterBulkCode_records_independent n hn R B hR hB mate hinv k reverse hQ hA l l' hl hl' hlen hlen']

/-- One directional program works for every valid geometry and matching. -/
theorem canonicalDirectionalCode_geometry_independent
    (n' : ℕ) (hn' : canonicalRouterStride n' ≤ n')
    (R' B' : ℕ) (hR' : 0 < R') (hB' : 1 ≤ B')
    (mate' : Fin n' → Fin n') (hinv' : Function.Involutive mate')
    (records : List (List (Fin (prime + K + 4))))
    (count : records.length = R' * 2 ^ n')
    (shape : ∀ row ∈ records, row.length = B' ∧ ∀ x ∈ row, x.val < 8)
    (Lb Lb' : ℕ) (rowBits rowBits' : List Bool) :
    canonicalDirectionalProgram n' hn' R' B' hR' hB' mate' hinv' k reverse hQ hA
      records count shape Lb' rowBits' =
      canonicalDirectionalProgram n hn R B hR hB mate hinv k reverse hQ hA l hl hlen Lb rowBits := by
  rfl

variable (Lb : ℕ) (rowBits : List Bool)

theorem canonicalClassCode_records_independent
    (data data' : CanonicalClassInput n hn R B hR hB mate hinv k hQ hA) :
    data.program Lb rowBits = data'.program Lb rowBits := by
  have hf (d : Fin 3) : data.directionProgram Lb rowBits d = data'.directionProgram Lb rowBits d :=
    canonicalDirectionalCode_records_independent n hn R B hR hB mate hinv k (decide (d = 1)) hQ hA
      (data'.records d) (data.records d) (data'.count d) (data.count d) (data'.shape d) (data.shape d) Lb rowBits
  unfold CanonicalClassInput.program
  rw [hf 0, hf 1, hf 2]

theorem canonicalMatchingCode_records_independent :
    canonicalMatchingProgram n hn R B hR hB mate hinv hQ hA l' hl' hlen' Lb rowBits =
      canonicalMatchingProgram n hn R B hR hB mate hinv hQ hA l hl hlen Lb rowBits := by
  unfold canonicalMatchingProgram
  apply congrArg₂ (fun x y : Pr Empty ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit => (show Pr Empty ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit from .seq x y))
  · apply congrArg₂ (fun x y : Pr Empty ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit => (show Pr Empty ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit from .seq x y))
    · exact canonicalClassCode_records_independent n hn R B hR hB mate hinv 2 hQ hA Lb rowBits _ _
    · exact canonicalClassCode_records_independent n hn R B hR hB mate hinv 1 hQ hA Lb rowBits _ _
  · exact canonicalClassCode_records_independent n hn R B hR hB mate hinv 0 hQ hA Lb rowBits _ _

theorem canonicalPermutationCode_records_independent (f : Equiv.Perm (Fin n)) :
    canonicalPermutationProgram n hn R B hR hB f hQ hA l' hl' hlen' Lb rowBits =
      canonicalPermutationProgram n hn R B hR hB f hQ hA l hl hlen Lb rowBits := by
  unfold canonicalPermutationProgram
  apply congrArg₂ (fun x y : Pr Empty ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit => (show Pr Empty ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit from .seq x y))
  · exact canonicalMatchingCode_records_independent n hn R B hR hB
      (fun q => f (permutationReflection f q)) (permutation_two_matchings f).2.1 hQ hA l l' hl hl' hlen hlen' Lb rowBits
  · exact canonicalMatchingCode_records_independent n hn R B hR hB
      (permutationReflection f) (permutation_two_matchings f).1 hQ hA
      (canonicalPermutationMiddle n hn R B hR hB f hQ hA l hl hlen)
      (canonicalPermutationMiddle n hn R B hR hB f hQ hA l' hl' hlen')
      (canonicalPermutationMiddle_count n hn R B hR hB f hQ hA l hl hlen)
      (canonicalPermutationMiddle_count n hn R B hR hB f hQ hA l' hl' hlen')
      (canonicalPermutationMiddle_shape n hn R B hR hB f hQ hA l hl hlen)
      (canonicalPermutationMiddle_shape n hn R B hR hB f hQ hA l' hl' hlen') Lb rowBits

/-- The complete schedule has fixed code across dimensions and coordinate permutations. -/
theorem canonicalPermutationCode_geometry_independent
    (n' : ℕ) (hn' : canonicalRouterStride n' ≤ n')
    (R' B' : ℕ) (hR' : 0 < R') (hB' : 1 ≤ B')
    (f : Equiv.Perm (Fin n)) (f' : Equiv.Perm (Fin n'))
    (records : List (List (Fin (prime + K + 4))))
    (count : records.length = R' * 2 ^ n')
    (shape : ∀ row ∈ records, row.length = B' ∧ ∀ x ∈ row, x.val < 8)
    (Lb' : ℕ) (rowBits' : List Bool) :
    canonicalPermutationProgram n' hn' R' B' hR' hB' f' hQ hA records count shape Lb' rowBits' =
      canonicalPermutationProgram n hn R B hR hB f hQ hA l hl hlen Lb rowBits := by
  rfl

/-- The eighteen-direction program depends only on dimensions and the coordinate permutation. -/
def canonicalPermutationCode (f : Equiv.Perm (Fin n)) :
    Pr Empty ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit :=
  canonicalPermutationProgram n hn R B hR hB f hQ hA
    (canonicalRouterZeroRecords n R B) (canonicalRouterZeroRecords_count n R B)
    (canonicalRouterZeroRecords_shape n R B) Lb rowBits

theorem canonicalPermutationProgram_eq_code (f : Equiv.Perm (Fin n)) :
    canonicalPermutationProgram n hn R B hR hB f hQ hA l hl hlen Lb rowBits =
      canonicalPermutationCode n hn R B hR hB hQ hA Lb rowBits f :=
  canonicalPermutationCode_records_independent n hn R B hR hB hQ hA
    (canonicalRouterZeroRecords n R B) l (canonicalRouterZeroRecords_count n R B) hl
    (canonicalRouterZeroRecords_shape n R B) hlen Lb rowBits f

/-- Restored execution with record-independent code/metadata and a dimension-only cost bound.
The metadata still has to be supplied; its production is a separate obligation. -/
theorem canonicalPermutationCode_exec (f : Equiv.Perm (Fin n)) (hnB : n ≤ B)
    (v : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit)
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (ready : FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B S)
    (hstream : S.R (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream) = l.flatten)
    (hinput : S.R (framedCoreAux (canonicalRouterCommonT + 3) 0) =
      canonicalPermutationMetadata n hn R B hR hB f hQ hA
        (canonicalScalarWidth n) (canonicalScalarWidth B) (GrowingCounterData.advance R []))
    (hsaved : S.R (framedCoreAux (canonicalRouterCommonT + 3) 2) = []) :
    ∃ (v' : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ canonicalPermutationCostBound n R B
        (canonicalScalarWidth n) (canonicalScalarWidth B) (R.log2 + 1) ∧
      Exec Empty.elim (.seq
        (canonicalPermutationCode n hn R B hR hB hQ hA
          (canonicalScalarWidth B) (GrowingCounterData.advance R []) f)
        (moveR (framedCoreAux (canonicalRouterCommonT + 3) 2)
          (framedCoreAux (canonicalRouterCommonT + 3) 0) id)) (mk v S) steps
        (mk v' { S with R := (Function.update S.R
          (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream)
          (List.flatten (moveRecs (canonicalPermutationRank n hn R B hR hB f hQ hA l hl hlen) l))) }) := by
  have he := canonicalPermutation_canonical_exec n hn R B hR hB f hQ hA l hl hlen hnB v S ready hstream
    (hinput.trans (canonicalPermutationFrame_eq_metadata n hn R B hR hB f hQ hA
      (canonicalScalarWidth n) (canonicalScalarWidth B) (GrowingCounterData.advance R []) l hl hlen).symm) hsaved
  rw [canonicalPermutationCost_eq_budget n hn R B hR hB f hQ hA
    (canonicalScalarWidth n) (canonicalScalarWidth B) (GrowingCounterData.advance R []) l hl hlen,
    canonicalPermutationProgram_eq_code n hn R B hR hB hQ hA l hl hlen
      (canonicalScalarWidth B) (GrowingCounterData.advance R []) f] at he
  obtain ⟨v', steps, hu, hcost, hexec⟩ := he
  exact ⟨v', steps, hu, hcost.trans (canonicalPermutationBudget_canonical_le n hn R B hR hB f hQ hA), hexec⟩

end
end IntegerMultBounds.MathlibTM2.Routing
