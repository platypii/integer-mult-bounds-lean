module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingProductionLayout

/-! A declared bank for the fixed matching producer. Only four external tapes
carry input: binary byte count, full matching table, stride and residue. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {N A : ℕ}

def matchingWorkspaceWords (count table stride residue : List (Fin (A + 4))) (j : ℕ) : List (Fin (A + 4)) :=
  if j = 0 then count else if j = 5 then table else if j = 8 then stride else if j = 18 then residue else []

noncomputable def matchingProductionBank (coreWords : Fin N → List (Fin (A + 4)))
    (count table stride residue : List (Fin (A + 4))) : Fin (N + 36) → List (Fin (A + 4)) :=
  Function.extend (matchingCoreEmbed N) coreWords
    (fun j => matchingWorkspaceWords count table stride residue (j.val - N))

/-- The four producer operands add no dependence on the live record stream. -/
theorem matchingProductionBank_length_le (coreWords : Fin N → List (Fin (A + 4)))
    (count table stride residue : List (Fin (A + 4))) (str : Fin N) (C : ℕ)
    (hcore : ∀ j, j ≠ str → (coreWords j).length ≤ C)
    (j : Fin (N + 36)) (hj : j ≠ matchingCoreEmbed N str) :
    (matchingProductionBank coreWords count table stride residue j).length ≤
      C + count.length + table.length + stride.length + residue.length := by
  by_cases hc : ∃ i, matchingCoreEmbed N i = j
  · obtain ⟨i, rfl⟩ := hc
    unfold matchingProductionBank
    rw [(matchingCoreEmbed_injective N).extend_apply]
    have hi := hcore i (fun he => hj (congrArg (matchingCoreEmbed N) he))
    omega
  · unfold matchingProductionBank
    rw [Function.extend_apply' _ _ _ hc]
    unfold matchingWorkspaceWords
    split_ifs <;> first | omega | exact Nat.zero_le _

theorem matchingProductionBank_core (coreWords : Fin N → List (Fin (A + 4)))
    (count table stride residue : List (Fin (A + 4))) (j : Fin N) :
    matchingProductionBank coreWords count table stride residue (matchingCoreEmbed N j) = coreWords j :=
  (matchingCoreEmbed_injective N).extend_apply _ _ j

theorem matchingProductionBank_work (coreWords : Fin N → List (Fin (A + 4)))
    (count table stride residue : List (Fin (A + 4))) (j : ℕ) (hj : j < 36) :
    matchingProductionBank coreWords count table stride residue ⟨N + j, by omega⟩ =
      matchingWorkspaceWords count table stride residue j := by
  have hoff : ¬∃ i, matchingCoreEmbed N i = (⟨N + j, by omega⟩ : Fin (N + 36)) := by
    rintro ⟨i, hi⟩
    have hv : i.val = N + j := congrArg (fun x : Fin (N + 36) => x.val) hi
    have := i.isLt
    omega
  unfold matchingProductionBank
  rw [Function.extend_apply' _ _ _ hoff]
  simp

theorem matchingProductionBank_extract (coreWords : Fin N → List (Fin (A + 4)))
    (count table stride residue : List (Fin (A + 4))) (j : Fin 8) :
    matchingProductionBank coreWords count table stride residue (matchingExtractSlot N j) =
      matchingWorkspaceWords count table stride residue
        (if j.val = 6 then 21 else if j.val < 6 then j.val else j.val - 1) := by
  apply matchingProductionBank_work
  have := j.isLt
  split_ifs <;> omega

theorem matchingProductionBank_gather (coreWords : Fin N → List (Fin (A + 4)))
    (count table stride residue : List (Fin (A + 4))) (j : Fin 18) :
    matchingProductionBank coreWords count table stride residue (matchingGatherSlot N j) =
      matchingWorkspaceWords count table stride residue (7 + j.val) := by
  convert matchingProductionBank_work coreWords count table stride residue (7 + j.val) (by have := j.isLt; omega) using 1
  congr 1
  apply Fin.ext
  dsimp only [matchingGatherSlot]
  omega

theorem matchingProductionBank_generate (coreWords : Fin N → List (Fin (A + 4)))
    (count table stride residue : List (Fin (A + 4))) (j : Fin 11) :
    matchingProductionBank coreWords count table stride residue (matchingGenerateSlot N j) = [] := by
  have hindex : matchingGenerateSlot N j = (⟨N + (25 + j.val), by have := j.isLt; omega⟩ : Fin (N + 36)) := by
    apply Fin.ext
    dsimp only [matchingGenerateSlot]
    omega
  rw [hindex, matchingProductionBank_work coreWords count table stride residue (25 + j.val) (by have := j.isLt; omega)]
  simp only [matchingWorkspaceWords, ite_eq_right (show 25 + j.val ≠ 0 by omega),
    ite_eq_right (show 25 + j.val ≠ 5 by omega), ite_eq_right (show 25 + j.val ≠ 8 by omega),
    ite_eq_right (show 25 + j.val ≠ 18 by omega)]

/-- A changing core register never changes the four external production inputs. -/
theorem matchingProductionBank_updateCore (coreWords : Fin N → List (Fin (A + 4)))
    (count table stride residue : List (Fin (A + 4))) (i : Fin N) (word : List (Fin (A + 4))) :
    matchingProductionBank (Function.update coreWords i word) count table stride residue =
      Function.update (matchingProductionBank coreWords count table stride residue) (matchingCoreEmbed N i) word := by
  funext j
  by_cases hcore : ∃ k, matchingCoreEmbed N k = j
  · obtain ⟨k, rfl⟩ := hcore
    rw [matchingProductionBank_core]
    by_cases hk : k = i
    · subst k; simp
    · rw [Function.update_of_ne hk, Function.update_of_ne ((matchingCoreEmbed_injective N).ne hk),
        matchingProductionBank_core]
  · have hj : j ≠ matchingCoreEmbed N i := fun h => hcore ⟨i, h.symm⟩
    rw [Function.update_of_ne hj]
    unfold matchingProductionBank
    rw [Function.extend_apply' _ _ _ hcore, Function.extend_apply' _ _ _ hcore]

end IntegerMultBounds.MathlibTM2.Routing
