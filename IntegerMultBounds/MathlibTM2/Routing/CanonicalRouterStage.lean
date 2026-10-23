module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterInput
public import IntegerMultBounds.MathlibTM2.Routing.FramedOriginalMatchingSchedule

/-! The actual canonical residue inputs discharge the repeated scheduler's
stage-data premises. All residues use the same original-matching program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section


/-- Original matching tables use only bits and separators. -/
theorem matchingEntryWords_small {A : ℕ} (L : ℕ) (entries : List (ℕ × ℕ)) :
    ∀ x ∈ (matchingEntryWords L entries : List (Fin (A + 4))), x.val < 8 := by
  induction entries with
  | nil => simp [matchingEntryWords]
  | cons entry entries ih =>
    intro x hx
    simp only [matchingEntryWords, matchingEntryWord, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with (hx | (rfl | (hx | rfl))) | hx
    · exact canonicalScalarWord_small _ _ x hx
    · change 3 < 8
      omega
    · exact canonicalScalarWord_small _ _ x hx
    · change 3 < 8
      omega
    · exact ih x hx


theorem matchingInitialBank_small {N A : ℕ} (core : Fin N → List (Fin (A + 4)))
    (p : Par) (mate : Fin p.wy → Fin p.wy) (Li Lk Lc : ℕ)
    (hcore : ∀ j, ∀ x ∈ core j, x.val < 8) :
    ∀ j, ∀ x ∈ matchingInitialBank core p mate Li Lk Lc j, x.val < 8 := by
  intro j
  by_cases hc : ∃ i, matchingCoreEmbed N i = j
  · obtain ⟨i, rfl⟩ := hc
    simpa only [matchingInitialBank, matchingProductionBank_core] using hcore i
  · unfold matchingInitialBank matchingProductionBank
    rw [Function.extend_apply' _ _ _ hc]
    unfold matchingWorkspaceWords
    split
    · exact canonicalScalarWord_small _ _
    · split
      · exact matchingEntryWords_small _ _
      · split
        · exact canonicalScalarWord_small _ _
        · split
          · exact canonicalScalarWord_small _ _
          · simp

theorem originalMatchingInputBank_small {N A : ℕ}
    (repairWords : Fin (N + 36) → List (Fin (A + 4)))
    (producerWords : Fin 57 → List (Fin (A + 4)))
    (hrepair : ∀ j, ∀ x ∈ repairWords j, x.val < 8)
    (hproducer : ∀ j, ∀ x ∈ producerWords j, x.val < 8) :
    ∀ j, ∀ x ∈ originalMatchingInputBank N repairWords producerWords j, x.val < 8 := by
  intro j
  by_cases hr : ∃ i, originalMatchingRepairEmbed N i = j
  · obtain ⟨i, rfl⟩ := hr
    rw [originalMatchingInputBank_repair]
    by_cases hi : i = matchingExtractSlot N 5
    · subst i
      rw [Function.update_self]
      simp
    · rw [Function.update_of_ne hi]
      exact hrepair i
  · unfold originalMatchingInputBank
    rw [Function.extend_apply' _ _ _ hr]
    exact hproducer _


theorem middleLookupMetadata_small {A n H w : ℕ} (hfit : 9 * H ≤ n) (hw : w ≤ H)
    (k : Fin 3) (L : ℕ) (inverse : Bool) :
    ∀ x ∈ (middleLookupMetadata n H hfit w hw k L inverse : List (Fin (A + 4))), x.val < 8 := by
  unfold middleLookupMetadata
  generalize reservoirCoordinateOrder inverse = stages
  induction stages with
  | nil => simp [delimitedScheduleInput]
  | cons i stages ih =>
    intro x hx
    simp only [delimitedScheduleInput, List.mem_append] at hx
    rcases hx with hx | hx
    · simp only [coordinateExchangeJobs, delimitedBankFrames, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with hx | rfl | hx | rfl | hx | rfl | hx | rfl
      all_goals first
        | exact canonicalScalarWord_small _ _ x hx
        | (change 3 < 8; omega)
    · exact ih x hx


theorem reservoirClassLocalBank_small {A n H w : ℕ} (hfit : 9 * H ≤ n) (hw : w ≤ H)
    (k : Fin 3) (L : ℕ) (mate : Fin n → Fin n) :
    ∀ j, ∀ x ∈ (reservoirClassLocalBank n H hfit w hw k L mate j : List (Fin (A + 4))), x.val < 8 := by
  have hlookup : ∀ j : Fin 33, ∀ x ∈ (reservoirMiddleLookupBank n H hfit w hw k L mate 0 j : List (Fin (A + 4))), x.val < 8 := by
    intro j
    unfold reservoirMiddleLookupBank
    repeat' first
      | split
      | exact canonicalScalarWord_small _ _
      | exact middleLookupMetadata_small hfit hw k L _
      | exact matchingEntryWords_small _ _
      | simp
  have hproduction : ∀ j : Fin 44, ∀ x ∈ (reservoirMiddleProductionBank n H hfit w hw k L mate j : List (Fin (A + 4))), x.val < 8 := by
    intro j
    unfold reservoirMiddleProductionBank
    split
    · exact hlookup _
    · split
      · exact canonicalScalarWord_small _ _
      · simp
  intro j
  unfold reservoirClassLocalBank
  split
  · rename_i hlt
    by_cases hj : (⟨j.val, hlt⟩ : Fin 44) = 21
    · rw [hj, Function.update_self]
      simp
    · rw [Function.update_of_ne hj]
      exact hproduction _
  · repeat' first
      | split
      | exact canonicalScalarWord_small _ _
      | exact matchingEntryWords_small _ _
      | simp

def canonicalRouterCountWidth (n : ℕ) (r : Fin (canonicalRouterStride n)) : ℕ :=
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  canonicalScalarWidth ((p.n * p.K) * (2 * (canonicalStageWidths p).coordinateBits + 2))

variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3) (reverse : Bool)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)

local notation "input" => canonicalRouterInput n hn R B hR hB mate hinv k reverse hQ hA l hl hlen

theorem canonicalRouterStage_data (r : Fin (canonicalRouterStride n)) :
    OriginalMatchingStageData (input r) (canonicalRouterCountWidth n r) (R * 2 ^ n) B n
      (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate hinv reverse := by
  let G := canonicalRouterGap n
  let stride := canonicalRouterStride n
  let p := routerProfileParameters n stride G r.val
  let localMate := canonicalRouterLocalMatching n hn k mate hinv
  refine { count := ?_, width := rfl, hn := ?_, hsize := ?_, hsource := ?_, hρ := ?_, htargets := ?_, hcountFit := ?_ }
  · change R * 2 ^ fieldsLen (selectiveLen p 0) = R * 2 ^ n
    rw [routerProfileFieldsLen n stride G hn r]
  · change n < 2 ^ (canonicalStageWidths p).coordinateBits
    have h := canonicalStageWidths_record p
    rw [routerProfileFieldsLen n stride G hn r] at h
    exact h
  · exact routerProfileParameters_width n stride G hn r
  · rfl
  · exact r.isLt
  · exact (routerLocalMatchingTargets n stride G hn r localMate
      (canonicalRouterLocalMatching_involutive n hn k mate hinv) reverse).symm
  · exact canonicalScalarWidth_fit _


theorem canonicalRouterStage_words (r : Fin (canonicalRouterStride n)) :
    ∀ j, ∀ x ∈ originalMatchingPlacedInputBank (input r) (canonicalRouterCountWidth n r) n
      (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate j,
      x.val < 8 := by
  unfold originalMatchingPlacedInputBank
  apply originalMatchingInputBank_small
  · unfold matchingPlacedInputBank
    apply matchingInitialBank_small
    intro j
    by_cases hj : j = (input r).coordinateRegister
    · subst j
      rw [Function.update_self]
      simp
    · rw [Function.update_of_ne hj]
      dsimp only [canonicalRouterInput]
      apply canonicalGeneratedInput_small
  · exact reservoirClassLocalBank_small _ _ _ _ _

/-- The concrete residue factory discharges the scheduler's program identity,
not merely its geometry and readiness facts. -/
theorem canonicalRouterStage_program (r s : Fin (canonicalRouterStride n)) :
    (originalMatchingPlacedProgram (input r) (originalMatchingProducerEmbed (inactiveClassifierPlacementT 6))
      (originalMatchingRepairEmbed (inactiveClassifierPlacementT 6)) Empty.elim Empty.elim k reverse :
        Pr Empty (originalMatchingScheduleT 6) Q (prime + K) Unit) =
    originalMatchingPlacedProgram (input s) (originalMatchingProducerEmbed (inactiveClassifierPlacementT 6))
      (originalMatchingRepairEmbed (inactiveClassifierPlacementT 6)) Empty.elim Empty.elim k reverse := by
  rfl

end
end IntegerMultBounds.MathlibTM2.Routing
