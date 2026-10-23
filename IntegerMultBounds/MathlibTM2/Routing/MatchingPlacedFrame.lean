module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingFixedPlacedRepair
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreMetadata

/-! Matching-derived calls retain fixed code, metadata and prices while their
record stream changes. These are the frame identities needed by a uniform loop. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K : ℕ} {P P' P'' U : Type}
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "str₀" => inactiveClassifierPlacementEmbed (t₀ := t₀) (classifierCore (inactiveConfigurationCore repairHost.src))

def matchingPlacedInputBank (input : GeneratedPlacedInput t₀ Q K P P' U) (Lc : ℕ) :=
  matchingInitialBank (Function.update input.M.R input.coordinateRegister [])
    input.p input.source input.w.indexBits input.w.strideBits Lc

theorem matchingPlacedInputBank_length_le (input : GeneratedPlacedInput t₀ Q K P P' U)
    (Lc C : ℕ) (hcore : ∀ j, j ≠ str₀ → (input.M.R j).length ≤ C)
    (j : Fin (TP₀ + 36)) (hj : j ≠ matchingCoreEmbed TP₀ str₀) :
    (matchingPlacedInputBank input Lc j).length ≤
      C + Lc + input.p.wy * (2 * (input.w.indexBits + input.w.strideBits) + 2) +
        input.w.strideBits + input.w.strideBits := by
  unfold matchingPlacedInputBank
  apply matchingInitialBank_length_le _ _ _ _ _ _ str₀ C ?_ j hj
  intro i hi
  rw [Function.update_apply]
  split
  · exact Nat.zero_le _
  · exact hcore i hi

variable (input : GeneratedPlacedInput t₀ Q K P P' U)
    (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = input.R * 2 ^ IntegerMultBounds.MathlibTM2.Layer.CompactDigits.fieldsLen (selectiveLen input.p input.X))
    (hlen : ∀ r ∈ l, r.length = input.B ∧ ∀ a ∈ r, a.val < 8)

theorem GeneratedPlacedInput.replaceRecords_matchingBank (Lc : ℕ) :
    matchingPlacedInputBank (input.replaceRecords l hl hlen) Lc =
      Function.update (matchingPlacedInputBank input Lc) (matchingCoreEmbed TP₀ str₀) l.flatten := by
  have hc := Function.update_comm input.coordinateRegister_ne_stream.symm l.flatten [] input.M.R
  dsimp only [matchingPlacedInputBank, GeneratedPlacedInput.replaceRecords, GeneratedPlacedInput.coordinateRegister]
  dsimp only [GeneratedPlacedInput.coordinateRegister] at hc
  rw [hc]
  exact matchingProductionBank_updateCore _ _ _ _ _ _ _

theorem GeneratedPlacedInput.replaceRecords_matchingPrice (Lc : ℕ) :
    matchingPlacedRepairPrice (input.replaceRecords l hl hlen) Lc = matchingPlacedRepairPrice input Lc := by
  dsimp only [matchingPlacedRepairPrice]
  rw [input.replaceRecords_price l hl hlen]
  dsimp only [GeneratedPlacedInput.replaceRecords, GeneratedPlacedInput.coordinateWords]

theorem GeneratedPlacedInput.replaceRecords_matchingProgram {T : ℕ} (e : Fin TP₀ → Fin T) (ι : P' → P'')
    (extract : Fin 8 → Fin T) (gather : Fin 18 → Fin T) (generate : Fin 11 → Fin T) (reverse : Bool) :
    matchingGeneratedPlacedProgram (input.replaceRecords l hl hlen) e ι extract gather generate reverse =
      matchingGeneratedPlacedProgram input e ι extract gather generate reverse := by
  dsimp only [matchingGeneratedPlacedProgram, GeneratedPlacedInput.replaceRecords, GeneratedPlacedInput.coordinateRegister]

theorem GeneratedPlacedInput.replaceRecords_matchingJobs {T : ℕ} (e : Fin (TP₀ + 36) → Fin T) (Lc : ℕ) :
    framedCoreJobs e (matchingCoreEmbed TP₀ str₀) (matchingPlacedInputBank (input.replaceRecords l hl hlen) Lc) =
      framedCoreJobs e (matchingCoreEmbed TP₀ str₀) (matchingPlacedInputBank input Lc) := by
  rw [input.replaceRecords_matchingBank l hl hlen, framedCoreJobs_updateStream]

end
end IntegerMultBounds.MathlibTM2.Routing
