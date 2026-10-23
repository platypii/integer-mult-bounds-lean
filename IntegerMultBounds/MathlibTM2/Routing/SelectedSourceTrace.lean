module

public import IntegerMultBounds.MathlibTM2.Routing.SelectedSourceLoop

/-! Exact final bank for raw selected-source generation: consumed input is in
the rewind archive and the accumulator contains the reversed complete profile. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

def selectedSourceProfileWord (Li Lk k : ℕ) (base : Fin 4 → ℕ) :
    List SelectedSourceChoice → List (Fin (A + 4))
  | [] => []
  | x :: xs => affineProfileFrames (Li + Lk) [(true, x.position k base)] ++
      selectedSourceProfileWord Li Lk k base xs

theorem selectedSourceProfileWord_profile (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List SelectedSourceChoice) :
    selectedSourceProfileWord (A := A) Li Lk k base xs =
      affineProfileFrames (Li + Lk) (xs.map (fun x => (true, x.position k base))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [selectedSourceProfileWord, affineProfileFrames, ih, List.append_assoc]

theorem selectedSourceProfileWord_length (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List SelectedSourceChoice) :
    (selectedSourceProfileWord (A := A) Li Lk k base xs).length = xs.length * (Li + Lk + 3) := by
  rw [selectedSourceProfileWord_profile, affineProfileFrames_length, List.length_map]

theorem selectedSourceTrace_keep (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List SelectedSourceChoice)
    (j : Fin T) (hs : j ≠ src) (ha : j ≠ saved) (hc : j ≠ accum) :
    selectedSourceTraceBank R src saved accum Li Lk k base xs j = R j := by
  induction xs generalizing R with
  | nil => rfl
  | cons x xs ih =>
    rw [selectedSourceTraceBank, ih]
    simp [selectedSourceReverseBank, hs, ha, hc]

theorem selectedSourceTrace_input (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (hss : src ≠ saved) (hsa : src ≠ accum) (Li Lk k : ℕ) (base : Fin 4 → ℕ)
    (xs : List SelectedSourceChoice) (hraw : R src = selectedSourceWords Li Lk xs) :
    selectedSourceTraceBank R src saved accum Li Lk k base xs src = [] := by
  induction xs generalizing R with
  | nil => exact hraw
  | cons x xs ih =>
    apply ih
    simp [selectedSourceReverseBank, hss, hsa]

theorem selectedSourceTrace_archive (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (hsa : saved ≠ accum) (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List SelectedSourceChoice) :
    selectedSourceTraceBank R src saved accum Li Lk k base xs saved =
      (selectedSourceWords Li Lk xs).reverse ++ R saved := by
  induction xs generalizing R with
  | nil => simp [selectedSourceTraceBank, selectedSourceWords]
  | cons x xs ih =>
    rw [selectedSourceTraceBank, ih]
    simp [selectedSourceReverseBank, selectedSourceWords, SelectedSourceChoice.word,
      List.reverse_append, List.append_assoc, hsa]

theorem selectedSourceTrace_output (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List SelectedSourceChoice) :
    selectedSourceTraceBank R src saved accum Li Lk k base xs accum =
      (selectedSourceProfileWord Li Lk k base xs).reverse ++ R accum := by
  induction xs generalizing R with
  | nil => simp [selectedSourceTraceBank, selectedSourceProfileWord]
  | cons x xs ih =>
    rw [selectedSourceTraceBank, ih]
    simp [selectedSourceReverseBank, selectedSourceProfileWord, SelectedSourceChoice.position,
      List.reverse_append, List.append_assoc]

def selectedSourceClosedBank (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List SelectedSourceChoice) :=
  Function.update (Function.update (Function.update R src []) saved
    ((selectedSourceWords Li Lk xs).reverse ++ R saved)) accum
    ((selectedSourceProfileWord Li Lk k base xs).reverse ++ R accum)

theorem selectedSourceTrace_closed (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (hss : src ≠ saved) (hsa : src ≠ accum) (haa : saved ≠ accum)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List SelectedSourceChoice)
    (hraw : R src = selectedSourceWords Li Lk xs) :
    selectedSourceTraceBank R src saved accum Li Lk k base xs =
      selectedSourceClosedBank R src saved accum Li Lk k base xs := by
  funext j
  by_cases hj : j = accum
  · subst j
    simp only [selectedSourceClosedBank, Function.update_self]
    exact selectedSourceTrace_output R src saved accum Li Lk k base xs
  · by_cases hs : j = saved
    · subst j
      simp only [selectedSourceClosedBank, Function.update_of_ne haa, Function.update_self]
      exact selectedSourceTrace_archive R src saved accum haa Li Lk k base xs
    · by_cases hc : j = src
      · subst j
        simp only [selectedSourceClosedBank, Function.update_of_ne hsa, Function.update_of_ne hss, Function.update_self]
        exact selectedSourceTrace_input R src saved accum hss hsa Li Lk k base xs hraw
      · simp only [selectedSourceClosedBank, Function.update_of_ne hj, Function.update_of_ne hs, Function.update_of_ne hc]
        exact selectedSourceTrace_keep R src saved accum Li Lk k base xs j hc hs hj

end IntegerMultBounds.MathlibTM2.Routing
