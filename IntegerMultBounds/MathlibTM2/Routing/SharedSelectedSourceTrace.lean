module

public import IntegerMultBounds.MathlibTM2.Routing.SharedSelectedSourceLoop

/-! Exact final bank for raw selected-source generation: consumed input is in
the rewind archive and the accumulator contains the reversed complete profile. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

def sharedSelectedSourceProfileWord (Li Lk k : ℕ) (base : Fin 4 → ℕ) :
    List GatedSelectedSourceChoice → List (Fin (A + 4))
  | [] => []
  | x :: xs => affineProfileFrames (Li + Lk) [(true, x.position k base)] ++
      sharedSelectedSourceProfileWord Li Lk k base xs

theorem sharedSelectedSourceProfileWord_profile (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice) :
    sharedSelectedSourceProfileWord (A := A) Li Lk k base xs =
      affineProfileFrames (Li + Lk) (xs.map (fun x => (true, x.position k base))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sharedSelectedSourceProfileWord, affineProfileFrames, ih, List.append_assoc]

theorem sharedSelectedSourceProfileWord_length (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice) :
    (sharedSelectedSourceProfileWord (A := A) Li Lk k base xs).length = xs.length * (Li + Lk + 3) := by
  rw [sharedSelectedSourceProfileWord_profile, affineProfileFrames_length, List.length_map]

theorem sharedSelectedSourceTrace_keep (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice)
    (j : Fin T) (hs : j ≠ src) (ha : j ≠ saved) (hc : j ≠ accum) :
    sharedSelectedSourceTraceBank R src saved accum Li Lk k base xs j = R j := by
  induction xs generalizing R with
  | nil => rfl
  | cons x xs ih =>
    rw [sharedSelectedSourceTraceBank, ih]
    simp [sharedSelectedSourceReverseBank, hs, ha, hc]

theorem sharedSelectedSourceTrace_input (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (hss : src ≠ saved) (hsa : src ≠ accum) (Li Lk k : ℕ) (base : Fin 4 → ℕ)
    (xs : List GatedSelectedSourceChoice) (hraw : R src = gatedSelectedSourceWords Li Lk xs) :
    sharedSelectedSourceTraceBank R src saved accum Li Lk k base xs src = [] := by
  induction xs generalizing R with
  | nil => exact hraw
  | cons x xs ih =>
    apply ih
    simp [sharedSelectedSourceReverseBank, hss, hsa]

theorem sharedSelectedSourceTrace_archive (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (hsa : saved ≠ accum) (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice) :
    sharedSelectedSourceTraceBank R src saved accum Li Lk k base xs saved =
      (gatedSelectedSourceWords Li Lk xs).reverse ++ R saved := by
  induction xs generalizing R with
  | nil => simp [sharedSelectedSourceTraceBank, gatedSelectedSourceWords]
  | cons x xs ih =>
    rw [sharedSelectedSourceTraceBank, ih]
    simp [sharedSelectedSourceReverseBank, gatedSelectedSourceWords, GatedSelectedSourceChoice.word,
      List.reverse_append, List.append_assoc, hsa]

theorem sharedSelectedSourceTrace_output (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice) :
    sharedSelectedSourceTraceBank R src saved accum Li Lk k base xs accum =
      (sharedSelectedSourceProfileWord Li Lk k base xs).reverse ++ R accum := by
  induction xs generalizing R with
  | nil => simp [sharedSelectedSourceTraceBank, sharedSelectedSourceProfileWord]
  | cons x xs ih =>
    rw [sharedSelectedSourceTraceBank, ih]
    simp [sharedSelectedSourceReverseBank, sharedSelectedSourceProfileWord, GatedSelectedSourceChoice.position,
      List.reverse_append, List.append_assoc]

def sharedSelectedSourceClosedBank (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice) :=
  Function.update (Function.update (Function.update R src []) saved
    ((gatedSelectedSourceWords Li Lk xs).reverse ++ R saved)) accum
    ((sharedSelectedSourceProfileWord Li Lk k base xs).reverse ++ R accum)

theorem sharedSelectedSourceTrace_closed (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (hss : src ≠ saved) (hsa : src ≠ accum) (haa : saved ≠ accum)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice)
    (hraw : R src = gatedSelectedSourceWords Li Lk xs) :
    sharedSelectedSourceTraceBank R src saved accum Li Lk k base xs =
      sharedSelectedSourceClosedBank R src saved accum Li Lk k base xs := by
  funext j
  by_cases hj : j = accum
  · subst j
    simp only [sharedSelectedSourceClosedBank, Function.update_self]
    exact sharedSelectedSourceTrace_output R src saved accum Li Lk k base xs
  · by_cases hs : j = saved
    · subst j
      simp only [sharedSelectedSourceClosedBank, Function.update_of_ne haa, Function.update_self]
      exact sharedSelectedSourceTrace_archive R src saved accum haa Li Lk k base xs
    · by_cases hc : j = src
      · subst j
        simp only [sharedSelectedSourceClosedBank, Function.update_of_ne hsa, Function.update_of_ne hss, Function.update_self]
        exact sharedSelectedSourceTrace_input R src saved accum hss hsa Li Lk k base xs hraw
      · simp only [sharedSelectedSourceClosedBank, Function.update_of_ne hj, Function.update_of_ne hs, Function.update_of_ne hc]
        exact sharedSelectedSourceTrace_keep R src saved accum Li Lk k base xs j hc hs hj

end IntegerMultBounds.MathlibTM2.Routing
