module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingFixedControls

/-! Prefix-count arithmetic reuses the fixed producer workspace before the
producer runs. Its output is the extractor count, separate from both controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {N A : ℕ}

def matchingFixedCountSlot (inputs : Fin 3 → Fin N) : Fin 13 → Fin (N + 36) :=
  ![matchingCoreEmbed N (inputs 0), matchingCoreEmbed N (inputs 1),
    matchingExtractSlot N 1, matchingExtractSlot N 2, matchingExtractSlot N 0,
    matchingExtractSlot N 3, matchingExtractSlot N 4, matchingExtractSlot N 7,
    matchingGatherSlot N 0, matchingGatherSlot N 2, matchingGatherSlot N 3,
    matchingCoreEmbed N (inputs 2), matchingGatherSlot N 4]

theorem matchingFixedCountSlot_injective (inputs : Fin 3 → Fin N)
    (hin : Function.Injective inputs) : Function.Injective (matchingFixedCountSlot inputs) := by
  have hinput (i j : Fin 3) : (inputs i).val = (inputs j).val ↔ i = j :=
    ⟨fun h => hin (Fin.ext h), fun h => congrArg (fun k => (inputs k).val) h⟩
  have h0 := (inputs 0).isLt
  have h1 := (inputs 1).isLt
  have h2 := (inputs 2).isLt
  have h01 : (inputs 0).val ≠ (inputs 1).val := fun h => (by decide : (0 : Fin 3) ≠ 1) ((hinput 0 1).mp h)
  have h02 : (inputs 0).val ≠ (inputs 2).val := fun h => (by decide : (0 : Fin 3) ≠ 2) ((hinput 0 2).mp h)
  have h12 : (inputs 1).val ≠ (inputs 2).val := fun h => (by decide : (1 : Fin 3) ≠ 2) ((hinput 1 2).mp h)
  intro i j h
  have hv := congrArg (fun k : Fin (N + 36) => k.val) h
  fin_cases i <;> fin_cases j <;>
    simp [matchingFixedCountSlot, matchingCoreEmbed, matchingExtractSlot,
      matchingGatherSlot] at hv <;> first | rfl | omega

theorem matchingFixedCountSlot_controls (inputs : Fin 3 → Fin N) (j : Fin 13) :
    matchingFixedCountSlot inputs j ≠ matchingGatherSlot N 1 ∧
      matchingFixedCountSlot inputs j ≠ matchingGatherSlot N 11 := by
  have h0 := (inputs 0).isLt
  have h1 := (inputs 1).isLt
  have h2 := (inputs 2).isLt
  fin_cases j <;>
    simp [matchingFixedCountSlot, matchingCoreEmbed, matchingExtractSlot,
      matchingGatherSlot, Fin.ext_iff] <;> omega

theorem matchingFixedCountBlank (inputs : Fin 3 → Fin N)
    (coreWords : Fin N → List (Fin (A + 4))) (table : List (Fin (A + 4)))
    (j : Fin 13) (h0 : j ≠ 0) (h1 : j ≠ 1) (h10 : j ≠ 10) (h11 : j ≠ 11) :
    matchingProductionBank coreWords [] table [] [] (matchingFixedCountSlot inputs j) = [] := by
  fin_cases j <;> simp_all [matchingFixedCountSlot, matchingProductionBank_extract,
    matchingProductionBank_gather, matchingWorkspaceWords]

theorem matchingFixedCount_gather (j : Fin 18) :
    matchingExtractSlot N 0 ≠ matchingGatherSlot N j := by
  intro h
  have hv := congrArg (fun k : Fin (N + 36) => k.val) h
  change N + 0 = N + 7 + j.val at hv
  omega

theorem matchingFixedCount_generate (j : Fin 11) :
    matchingExtractSlot N 0 ≠ matchingGenerateSlot N j := by
  intro h
  have hv := congrArg (fun k : Fin (N + 36) => k.val) h
  change N + 0 = N + 25 + j.val at hv
  omega

end IntegerMultBounds.MathlibTM2.Routing
