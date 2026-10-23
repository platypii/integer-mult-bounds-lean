module

public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankLoad

/-! Closed frame lengths and archive contents for uniform metadata-bank loading. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable {T A : ℕ}

theorem delimitedBankFrames_length (delimiter : Fin (A + 4))
    (jobs : List (Fin T × List (Fin (A + 4)))) :
    (delimitedBankFrames delimiter jobs).length =
      (jobs.map (fun j => j.2.length)).sum + jobs.length := by
  induction jobs with
  | nil => rfl
  | cons j jobs ih => simp only [delimitedBankFrames, List.length_append, List.length_cons,
      List.map_cons, List.sum_cons, ih]; omega

/-- Framing adds one delimiter per word. -/
theorem delimitedBankFrames_length_le (delimiter : Fin (A + 4))
    (jobs : List (Fin T × List (Fin (A + 4)))) (W : ℕ)
    (hwords : ∀ job ∈ jobs, job.2.length ≤ W) :
    (delimitedBankFrames delimiter jobs).length ≤ jobs.length * (W + 1) := by
  induction jobs with
  | nil => simp [delimitedBankFrames]
  | cons job jobs ih =>
    have hj := hwords job (by simp)
    have ht := ih (fun j hj => hwords j (by simp [hj]))
    simp only [delimitedBankFrames, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem delimitedBankLoadCost_frames (delimiter : Fin (A + 4))
    (jobs : List (Fin T × List (Fin (A + 4)))) :
    delimitedBankLoadCost jobs = 4 * (delimitedBankFrames delimiter jobs).length + 2 * jobs.length + 1 := by
  induction jobs with
  | nil => rfl
  | cons j jobs ih => simp only [delimitedBankLoadCost, delimitedBankFrames,
      List.length_append, List.length_cons, ih]; omega

theorem delimitedBankLoaded_keep (src tmp saved j : Fin T)
    (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (jobs : List (Fin T × List (Fin (A + 4))))
    (hsrc : j ≠ src) (htmp : j ≠ tmp) (hsaved : j ≠ saved)
    (hjobs : ∀ job ∈ jobs, j ≠ job.1) (R : Fin T → List (Fin (A + 4))) :
    delimitedBankLoaded src tmp saved delimiter rest jobs R j = R j := by
  induction jobs generalizing R with
  | nil => rfl
  | cons job jobs ih =>
    rw [delimitedBankLoaded, ih (fun x hx => hjobs x (by simp [hx]))]
    simp only [delimitedConfigurationLoaded, Function.update_of_ne hsrc,
      Function.update_of_ne htmp, Function.update_of_ne hsaved,
      Function.update_of_ne (hjobs job (by simp))]

theorem delimitedBankLoaded_archive (src tmp saved : Fin T)
    (delimiter : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (jobs : List (Fin T × List (Fin (A + 4))))
    (hjobs : ∀ job ∈ jobs, job.1 ≠ saved) (R : Fin T → List (Fin (A + 4))) :
    delimitedBankLoaded src tmp saved delimiter rest jobs R saved =
      (delimitedBankFrames delimiter jobs).reverse ++ R saved := by
  induction jobs generalizing R with
  | nil => rfl
  | cons job jobs ih =>
    rw [delimitedBankLoaded, ih (fun x hx => hjobs x (by simp [hx]))]
    simp [delimitedConfigurationLoaded,
      (hjobs job (by simp)).symm,
      delimitedBankFrames, List.reverse_append, List.reverse_cons, List.append_assoc]

end IntegerMultBounds.MathlibTM2.Routing
