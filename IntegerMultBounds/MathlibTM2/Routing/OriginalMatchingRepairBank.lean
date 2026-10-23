module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingProductionLayout
public import IntegerMultBounds.MathlibTM2.Host.Index

/-! One fixed bank shares only the generated local table between its producer
and repair. All other producer registers lie outside the complete repair bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {A : ℕ}

def originalMatchingRepairEmbed (N : ℕ) (j : Fin (N + 36)) : Fin (N + 36 + 57) := j.castAdd 57

def originalMatchingProducerEmbed (N : ℕ) (j : Fin 57) : Fin (N + 36 + 57) :=
  if j = 34 then originalMatchingRepairEmbed N (matchingExtractSlot N 5)
  else ⟨N + 36 + j.val, by have := j.isLt; omega⟩

theorem originalMatchingRepairEmbed_injective (N : ℕ) :
    Function.Injective (originalMatchingRepairEmbed N) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (N + 36 + 57) => x.val) h)

theorem originalMatchingProducer_off (N : ℕ) (j : Fin 57) (hj : j ≠ 34) (i : Fin (N + 36)) :
    originalMatchingProducerEmbed N j ≠ originalMatchingRepairEmbed N i := by
  intro h
  have hv := congrArg (fun x : Fin (N + 36 + 57) => x.val) h
  simp only [originalMatchingProducerEmbed, ite_eq_right hj, originalMatchingRepairEmbed, Fin.val_castAdd] at hv
  have := i.isLt
  omega

theorem originalMatchingProducerEmbed_injective (N : ℕ) :
    Function.Injective (originalMatchingProducerEmbed N) := by
  intro i j h
  by_cases hi : i = 34
  · subst i
    by_cases hj : j = 34
    · exact hj.symm
    · exact False.elim (originalMatchingProducer_off N j hj (matchingExtractSlot N 5) h.symm)
  by_cases hj : j = 34
  · subst j
    exact False.elim (originalMatchingProducer_off N i hi (matchingExtractSlot N 5) h)
  have hv := congrArg (fun x : Fin (N + 36 + 57) => x.val) h
  simp only [originalMatchingProducerEmbed, ite_eq_right hi, ite_eq_right hj] at hv
  apply Fin.ext
  omega

noncomputable def originalMatchingInputBank (N : ℕ)
    (repairWords : Fin (N + 36) → List (Fin (A + 4)))
    (producerWords : Fin 57 → List (Fin (A + 4))) : Fin (N + 36 + 57) → List (Fin (A + 4)) :=
  Function.extend (originalMatchingRepairEmbed N) (Function.update repairWords (matchingExtractSlot N 5) [])
    (fun j => producerWords ⟨j.val - (N + 36), by have := j.isLt; omega⟩)

/-- Joining producer and repair banks preserves a nonstream metadata bound. -/
theorem originalMatchingInputBank_length_le (N : ℕ)
    (repairWords : Fin (N + 36) → List (Fin (A + 4)))
    (producerWords : Fin 57 → List (Fin (A + 4))) (str : Fin (N + 36)) (C D : ℕ)
    (hrepair : ∀ j, j ≠ str → (repairWords j).length ≤ C)
    (hproducer : ∀ j, (producerWords j).length ≤ D)
    (j : Fin (N + 36 + 57)) (hj : j ≠ originalMatchingRepairEmbed N str) :
    (originalMatchingInputBank N repairWords producerWords j).length ≤ C + D := by
  by_cases hc : ∃ i, originalMatchingRepairEmbed N i = j
  · obtain ⟨i, rfl⟩ := hc
    unfold originalMatchingInputBank
    rw [(originalMatchingRepairEmbed_injective N).extend_apply, Function.update_apply]
    split
    · exact Nat.zero_le _
    · have hi := hrepair i (fun he => hj (congrArg (originalMatchingRepairEmbed N) he))
      omega
  · unfold originalMatchingInputBank
    rw [Function.extend_apply' _ _ _ hc]
    exact (hproducer _).trans (Nat.le_add_left _ _)

theorem originalMatchingInputBank_repair (N : ℕ)
    (repairWords : Fin (N + 36) → List (Fin (A + 4)))
    (producerWords : Fin 57 → List (Fin (A + 4))) (j : Fin (N + 36)) :
    originalMatchingInputBank N repairWords producerWords (originalMatchingRepairEmbed N j) =
      Function.update repairWords (matchingExtractSlot N 5) [] j :=
  (originalMatchingRepairEmbed_injective N).extend_apply _ _ j

theorem originalMatchingInputBank_producer (N : ℕ)
    (repairWords : Fin (N + 36) → List (Fin (A + 4)))
    (producerWords : Fin 57 → List (Fin (A + 4))) (hblank : producerWords 34 = []) (j : Fin 57) :
    originalMatchingInputBank N repairWords producerWords (originalMatchingProducerEmbed N j) = producerWords j := by
  by_cases hj : j = 34
  · subst j
    simp only [originalMatchingProducerEmbed, ite_true, originalMatchingInputBank_repair, Function.update_self, hblank]
  have hoff : ¬∃ i, originalMatchingRepairEmbed N i = originalMatchingProducerEmbed N j := by
    rintro ⟨i, hi⟩
    exact originalMatchingProducer_off N j hj i hi.symm
  unfold originalMatchingInputBank
  rw [Function.extend_apply' _ _ _ hoff]
  simp only [originalMatchingProducerEmbed, ite_eq_right hj]
  congr 1
  apply Fin.ext
  simp

theorem originalMatchingInputBank_updateRepair (N : ℕ)
    (repairWords : Fin (N + 36) → List (Fin (A + 4)))
    (producerWords : Fin 57 → List (Fin (A + 4))) (i : Fin (N + 36))
    (hi : i ≠ matchingExtractSlot N 5) (word : List (Fin (A + 4))) :
    originalMatchingInputBank N (Function.update repairWords i word) producerWords =
      Function.update (originalMatchingInputBank N repairWords producerWords) (originalMatchingRepairEmbed N i) word := by
  funext j
  by_cases hcore : ∃ k, originalMatchingRepairEmbed N k = j
  · obtain ⟨k, rfl⟩ := hcore
    rw [originalMatchingInputBank_repair]
    by_cases hk : k = i
    · subst k; simp only [Function.update_of_ne hi, Function.update_self]
    · rw [Function.update_of_ne ((originalMatchingRepairEmbed_injective N).ne hk), originalMatchingInputBank_repair]
      by_cases ht : k = matchingExtractSlot N 5
      · subst k; simp only [Function.update_self]
      · simp only [Function.update_of_ne ht, Function.update_of_ne hk]
  · have hj : j ≠ originalMatchingRepairEmbed N i := fun h => hcore ⟨i, h.symm⟩
    rw [Function.update_of_ne hj]
    unfold originalMatchingInputBank
    rw [Function.extend_apply' _ _ _ hcore, Function.extend_apply' _ _ _ hcore]

end IntegerMultBounds.MathlibTM2.Routing
