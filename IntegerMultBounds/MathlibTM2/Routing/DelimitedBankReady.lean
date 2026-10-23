module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankTrace
public import IntegerMultBounds.MathlibTM2.Routing.MetadataClean

/-! Readiness and cleanup identities for a reusable metadata bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable {T A : ℕ}

theorem delimitedBankLoaded_at (src tmp saved : Fin T)
    (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (jobs : List (Fin T × List (Fin (A + 4)))) (hdistinct : (jobs.map Prod.fst).Nodup)
    (hseparate : ∀ j ∈ jobs, j.1 ≠ src ∧ j.1 ≠ tmp ∧ j.1 ≠ saved)
    (job : Fin T × List (Fin (A + 4))) (hj : job ∈ jobs)
    (R : Fin T → List (Fin (A + 4))) :
    delimitedBankLoaded src tmp saved delimiter rest jobs R job.1 = job.2 := by
  induction jobs generalizing R with
  | nil => simp at hj
  | cons head jobs ih =>
    have hn := List.nodup_cons.mp hdistinct
    rcases List.mem_cons.mp hj with rfl | hj
    · obtain ⟨hjs, hjt, hja⟩ := hseparate job (by simp)
      have hout : ∀ x ∈ jobs, job.1 ≠ x.1 := by
        intro x hx he
        exact hn.1 (List.mem_map.mpr ⟨x, hx, he.symm⟩)
      rw [delimitedBankLoaded, delimitedBankLoaded_keep src tmp saved job.1 delimiter rest jobs
        hjs hjt hja hout]
      simp [delimitedConfigurationLoaded]
    · rw [delimitedBankLoaded]
      exact ih hn.2 (fun x hx => hseparate x (by simp [hx])) hj _

theorem delimitedBankLoaded_src (src tmp saved : Fin T) (hst : src ≠ tmp) (hsa : src ≠ saved)
    (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (jobs : List (Fin T × List (Fin (A + 4)))) (hjobs : ∀ job ∈ jobs, job.1 ≠ src)
    (R : Fin T → List (Fin (A + 4))) (hsrc : R src = delimitedBankFrames delimiter jobs ++ rest) :
    delimitedBankLoaded src tmp saved delimiter rest jobs R src = rest := by
  induction jobs generalizing R with
  | nil => simpa only [delimitedBankFrames, delimitedBankLoaded, List.nil_append] using hsrc
  | cons job jobs ih =>
    rw [delimitedBankLoaded]
    apply ih (fun x hx => hjobs x (by simp [hx]))
    simp [delimitedConfigurationLoaded, (hjobs job (by simp)).symm, hst, hsa]

theorem delimitedBankLoaded_tmp (src tmp saved : Fin T) (hta : tmp ≠ saved)
    (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (jobs : List (Fin T × List (Fin (A + 4)))) (hjobs : ∀ job ∈ jobs, job.1 ≠ tmp)
    (R : Fin T → List (Fin (A + 4))) (htmp : R tmp = []) :
    delimitedBankLoaded src tmp saved delimiter rest jobs R tmp = [] := by
  induction jobs generalizing R with
  | nil => exact htmp
  | cons job jobs ih =>
    rw [delimitedBankLoaded]
    apply ih (fun x hx => hjobs x (by simp [hx]))
    simp [delimitedConfigurationLoaded, (hjobs job (by simp)).symm, hta]

/-- Erasing the loaded bank restores all reusable registers; only the input
cursor and its complete archive retain the consumed frame. -/
theorem delimitedBankLoaded_clean (src tmp saved : Fin T) (hreg : [src, tmp, saved].Nodup)
    (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (jobs : List (Fin T × List (Fin (A + 4))))
    (hseparate : ∀ j ∈ jobs, j.1 ≠ src ∧ j.1 ≠ tmp ∧ j.1 ≠ saved)
    (R : Fin T → List (Fin (A + 4)))
    (hsrc : R src = delimitedBankFrames delimiter jobs ++ rest) (htmp : R tmp = [])
    (hblank : ∀ j ∈ jobs, R j.1 = []) :
    metadataCleared (delimitedBankLoaded src tmp saved delimiter rest jobs R) (jobs.map Prod.fst) =
      Function.update (Function.update R src rest) saved ((delimitedBankFrames delimiter jobs).reverse ++ R saved) := by
  have hn := hreg
  regs_ne hn
  funext j
  by_cases hj : j ∈ jobs.map Prod.fst
  · rw [metadataCleared_at _ _ j hj]
    obtain ⟨job, hjob, rfl⟩ := List.mem_map.mp hj
    obtain ⟨hjs, _, hja⟩ := hseparate job hjob
    simp [hjs, hja, hblank job hjob]
  · rw [metadataCleared_keep _ _ j hj]
    by_cases hs : j = src
    · subst j
      rw [delimitedBankLoaded_src src tmp saved ‹src ≠ tmp› ‹src ≠ saved› delimiter rest jobs
        (fun job hj => (hseparate job hj).1) R hsrc]
      simp [‹src ≠ saved›]
    · by_cases ha : j = saved
      · subst j
        rw [delimitedBankLoaded_archive src tmp saved delimiter rest jobs
          (fun job hj => (hseparate job hj).2.2) R]
        simp
      · by_cases ht : j = tmp
        · subst j
          rw [delimitedBankLoaded_tmp src tmp saved ‹tmp ≠ saved› delimiter rest jobs
            (fun job hj => (hseparate job hj).2.1) R htmp]
          simp [‹src ≠ tmp›.symm, ‹tmp ≠ saved›, htmp]
        · rw [Function.update_of_ne ha, Function.update_of_ne hs]
          apply delimitedBankLoaded_keep src tmp saved j delimiter rest jobs hs ht ha
          intro job hjob he
          exact hj (List.mem_map.mpr ⟨job, hjob, he.symm⟩)

/-- Clearing any loaded bank costs exactly twice its encoded frame length plus one. -/
theorem metadataCleanCost_framed (delimiter : Fin (A + 4))
    (jobs : List (Fin T × List (Fin (A + 4)))) (R : Fin T → List (Fin (A + 4)))
    (hwords : ∀ job ∈ jobs, R job.1 = job.2) :
    metadataCleanCost R (jobs.map Prod.fst) = 2 * (delimitedBankFrames delimiter jobs).length + 1 := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
    rw [List.map_cons, metadataCleanCost, ih (fun j hj => hwords j (by simp [hj])),
      hwords job (by simp)]
    simp only [delimitedBankFrames, List.length_append, List.length_cons]
    omega

end IntegerMultBounds.MathlibTM2.Routing
