module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankCopy
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreMetadata

/-! Execute encoding of every nonstream core register into a reusable metadata
frame. The fixed register list excludes the changing record stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {N T Q A : ℕ} {P U : Type}

theorem framedCoreCopy_exec (body : P → Pr P T Q A U)
    (e : Fin N → Fin T) (str : Fin N) (dst tmp work : Fin T)
    (hreg : [dst, tmp, work].Nodup)
    (hoff : ∀ j, e j ≠ dst ∧ e j ≠ tmp ∧ e j ≠ work)
    (delimiter : Fin (A + 4)) (words : Fin N → List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hwords : ∀ j, j ≠ str → S.R (e j) = words j)
    (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (delimitedBankCopy dst tmp work delimiter (framedCoreDestinations e str)) (mk v S)
        (6 * (delimitedBankFrames delimiter (framedCoreJobs e str words)).length +
          (framedCoreJobs e str words).length + 1)
        (mk v' { S with R := (Function.update S.R dst
          (delimitedBankFrames delimiter (framedCoreJobs e str words) ++ S.R dst)) }) := by
  have hsep : ∀ job ∈ framedCoreJobs e str words,
      job.1 ≠ dst ∧ job.1 ≠ tmp ∧ job.1 ≠ work := by
    intro job hj
    change job ∈ (framedCoreRegisters str).map (fun j => (e j, words j)) at hj
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hj
    exact hoff j
  have hdata : ∀ job ∈ framedCoreJobs e str words, S.R job.1 = job.2 := by
    intro job hj
    change job ∈ (framedCoreRegisters str).map (fun j => (e j, words j)) at hj
    obtain ⟨j, hmem, rfl⟩ := List.mem_map.mp hj
    exact hwords j ((mem_framedCoreRegisters str j).mp hmem)
  obtain ⟨v', hu, he⟩ := delimitedBankCopy_exec body dst tmp work hreg delimiter
    (framedCoreJobs e str words) hsep v S hdata htmp hwork
  rw [delimitedBankCopyCost_eq delimiter] at he
  refine ⟨v', hu, ?_⟩
  simpa only [framedCoreJobs, framedCoreDestinations, List.map_map, Function.comp_def] using he

/-- Serialization is linear in the uniform bank bound, not in live payload. -/
theorem framedCoreCopyCost_le (e : Fin N → Fin T) (str : Fin N)
    (delimiter : Fin (A + 4)) (words : Fin N → List (Fin (A + 4)))
    (W : ℕ) (hwords : ∀ j, j ≠ str → (words j).length ≤ W) :
    6 * (delimitedBankFrames delimiter (framedCoreJobs e str words)).length +
      (framedCoreJobs e str words).length + 1 ≤ 6 * (N * (W + 1)) + N + 1 := by
  have hf := framedCoreFrames_length_le delimiter e str words W hwords
  have hj := framedCoreJobs_length_le e str words
  omega

end IntegerMultBounds.MathlibTM2.Routing
