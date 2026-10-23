module

public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreBank

/-! A stage's encoded metadata does not include its changing record stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable {N T A : ℕ}

theorem framedCoreJobs_congr (e : Fin N → Fin T) (str : Fin N)
    (words words' : Fin N → List (Fin (A + 4)))
    (hwords : ∀ j, j ≠ str → words j = words' j) :
    framedCoreJobs e str words = framedCoreJobs e str words' := by
  unfold framedCoreJobs
  apply List.map_congr_left
  intro j hj
  rw [hwords j ((mem_framedCoreRegisters str j).mp hj)]

theorem framedCoreJobs_updateStream (e : Fin N → Fin T) (str : Fin N)
    (words : Fin N → List (Fin (A + 4))) (stream : List (Fin (A + 4))) :
    framedCoreJobs e str (Function.update words str stream) = framedCoreJobs e str words := by
  apply framedCoreJobs_congr
  intro j hj
  exact Function.update_of_ne hj _ _

theorem framedCoreFrames_updateStream (e : Fin N → Fin T) (str : Fin N)
    (delimiter : Fin (A + 4)) (words : Fin N → List (Fin (A + 4))) (stream : List (Fin (A + 4))) :
    delimitedBankFrames delimiter (framedCoreJobs e str (Function.update words str stream)) =
      delimitedBankFrames delimiter (framedCoreJobs e str words) := by
  rw [framedCoreJobs_updateStream]

theorem framedCoreRegisters_ne_nil (str : Fin N) (hN : 2 ≤ N) : framedCoreRegisters str ≠ [] := by
  let z : Fin N := ⟨0, by omega⟩
  let o : Fin N := ⟨1, by omega⟩
  have hzo : z ≠ o := by intro he; have hv := congrArg Fin.val he; change 0 = 1 at hv; omega
  have hex : ∃ j : Fin N, j ≠ str := by
    by_cases hz : z = str
    · exact ⟨o, fun ho => hzo (hz.trans ho.symm)⟩
    · exact ⟨z, hz⟩
  obtain ⟨j, hj⟩ := hex
  intro he
  have hm := (mem_framedCoreRegisters str j).mpr hj
  simp only [he, List.not_mem_nil] at hm

end IntegerMultBounds.MathlibTM2.Routing
