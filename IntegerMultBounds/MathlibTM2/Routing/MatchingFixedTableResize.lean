module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingProductionBank
public import IntegerMultBounds.MathlibTM2.Routing.MatchingTableResizeScope

/-! Table re-encoding reuses the fixed producer scratch before compilation. Its
resized output occupies the extractor table slot, with two compact core inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {N A : ℕ}

def matchingFixedTableResizeSlot (inputs : Fin 2 → Fin N) : Fin 14 → Fin (N + 36) :=
  ![matchingCoreEmbed N (inputs 0),
    matchingGenerateSlot N 0, matchingGenerateSlot N 1, matchingGenerateSlot N 2,
    matchingGenerateSlot N 3, matchingGenerateSlot N 4, matchingGenerateSlot N 5,
    matchingGenerateSlot N 6, matchingGenerateSlot N 7, matchingGenerateSlot N 8,
    matchingCoreEmbed N (inputs 1), matchingGenerateSlot N 9, matchingGenerateSlot N 10,
    matchingGatherSlot N 14]

theorem matchingFixedTableResizeSlot_injective (inputs : Fin 2 → Fin N)
    (hin : Function.Injective inputs) : Function.Injective (matchingFixedTableResizeSlot inputs) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [matchingFixedTableResizeSlot, (matchingCoreEmbed_injective N).eq_iff,
      hin.eq_iff, (matchingGenerateSlot_injective N).eq_iff,
      matchingCoreEmbed_generate, matchingCoreEmbed_gather, matchingGenerateSlot_gather,
      Ne.symm (matchingCoreEmbed_generate N _ _), Ne.symm (matchingCoreEmbed_gather N _ _),
      Ne.symm (matchingGenerateSlot_gather N _ _)]

theorem matchingFixedTableResizeSlot_table (inputs : Fin 2 → Fin N) (j : Fin 14) :
    matchingExtractSlot N 5 ≠ matchingFixedTableResizeSlot inputs j := by
  have h0 := (inputs 0).isLt
  have h1 := (inputs 1).isLt
  fin_cases j <;> simp [matchingFixedTableResizeSlot, matchingCoreEmbed,
    matchingGenerateSlot, matchingGatherSlot, matchingExtractSlot, Fin.ext_iff] <;> omega

theorem matchingFixedTableResizeBlank (inputs : Fin 2 → Fin N)
    (coreWords : Fin N → List (Fin (A + 4))) (count table stride residue : List (Fin (A + 4)))
    (j : Fin 14) (h0 : j ≠ 0) (h10 : j ≠ 10) :
    matchingProductionBank coreWords count table stride residue (matchingFixedTableResizeSlot inputs j) = [] := by
  fin_cases j <;> simp_all [matchingFixedTableResizeSlot, matchingProductionBank_generate,
    matchingProductionBank_gather, matchingWorkspaceWords]

theorem matchingProductionBank_update_table
    (coreWords : Fin N → List (Fin (A + 4)))
    (count table stride residue word : List (Fin (A + 4))) :
    Function.update (matchingProductionBank coreWords count table stride residue)
      (matchingExtractSlot N 5) word = matchingProductionBank coreWords count word stride residue := by
  funext j
  by_cases hc : j.val < N
  · let i : Fin N := ⟨j.val, hc⟩
    have hj : j = matchingCoreEmbed N i := by apply Fin.ext; rfl
    rw [hj, Function.update_of_ne (matchingCoreEmbed_extract N i 5),
      matchingProductionBank_core, matchingProductionBank_core]
  · have hj : j = (⟨N + (j.val - N), by have := j.isLt; omega⟩ : Fin (N + 36)) := by
      apply Fin.ext
      dsimp
      omega
    have hb : j.val - N < 36 := by have := j.isLt; omega
    by_cases ht : j = matchingExtractSlot N 5
    · subst j
      simp [matchingProductionBank_extract, matchingWorkspaceWords]
    · rw [Function.update_of_ne ht, hj, matchingProductionBank_work _ _ _ _ _ _ hb,
        matchingProductionBank_work _ _ _ _ _ _ hb]
      have h5 : j.val - N ≠ 5 := by
        intro h
        apply ht
        apply Fin.ext
        dsimp [matchingExtractSlot]
        omega
      simp [matchingWorkspaceWords, h5]

end IntegerMultBounds.MathlibTM2.Routing
