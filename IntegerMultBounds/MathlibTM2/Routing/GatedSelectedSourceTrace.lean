module

public import IntegerMultBounds.MathlibTM2.Routing.GatedSelectedSourceLoop

/-! Exact final bank for raw selected-source generation: consumed input is in
the rewind archive and the accumulator contains the reversed complete profile. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

def gatedSelectedSourceProfileWord (Li Lk k : ℕ) (base : Fin 4 → ℕ) :
    List GatedSelectedSourceChoice → List (Fin (A + 4))
  | [] => []
  | x :: xs => affineProfileFrames (Li + Lk) [(x.enabled, if x.enabled then x.position k base else 0)] ++
      gatedSelectedSourceProfileWord Li Lk k base xs

theorem gatedSelectedSourceProfileWord_profile (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice) :
    gatedSelectedSourceProfileWord (A := A) Li Lk k base xs =
      affineProfileFrames (Li + Lk) (xs.map (fun x => (x.enabled, if x.enabled then x.position k base else 0))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [gatedSelectedSourceProfileWord, affineProfileFrames, ih, List.append_assoc]

theorem gatedSelectedSourceProfileWord_length (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice) :
    (gatedSelectedSourceProfileWord (A := A) Li Lk k base xs).length = xs.length * (Li + Lk + 3) := by
  rw [gatedSelectedSourceProfileWord_profile, affineProfileFrames_length, List.length_map]

theorem gatedSelectedSourceTrace_keep (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice)
    (j : Fin T) (hs : j ≠ src) (ha : j ≠ saved) (hc : j ≠ accum) :
    gatedSelectedSourceTraceBank R src saved accum Li Lk k base xs j = R j := by
  induction xs generalizing R with
  | nil => rfl
  | cons x xs ih =>
    rw [gatedSelectedSourceTraceBank, ih]
    simp [gatedSelectedSourceReverseBank, hs, ha, hc]

theorem gatedSelectedSourceTrace_input (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (hss : src ≠ saved) (hsa : src ≠ accum) (Li Lk k : ℕ) (base : Fin 4 → ℕ)
    (xs : List GatedSelectedSourceChoice) (hraw : R src = gatedSelectedSourceWords Li Lk xs) :
    gatedSelectedSourceTraceBank R src saved accum Li Lk k base xs src = [] := by
  induction xs generalizing R with
  | nil => exact hraw
  | cons x xs ih =>
    apply ih
    simp [gatedSelectedSourceReverseBank, hss, hsa]

theorem gatedSelectedSourceTrace_archive (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (hsa : saved ≠ accum) (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice) :
    gatedSelectedSourceTraceBank R src saved accum Li Lk k base xs saved =
      (gatedSelectedSourceWords Li Lk xs).reverse ++ R saved := by
  induction xs generalizing R with
  | nil => simp [gatedSelectedSourceTraceBank, gatedSelectedSourceWords]
  | cons x xs ih =>
    rw [gatedSelectedSourceTraceBank, ih]
    simp [gatedSelectedSourceReverseBank, gatedSelectedSourceWords, GatedSelectedSourceChoice.word,
      List.reverse_append, List.append_assoc, hsa]

theorem gatedSelectedSourceTrace_output (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice) :
    gatedSelectedSourceTraceBank R src saved accum Li Lk k base xs accum =
      (gatedSelectedSourceProfileWord Li Lk k base xs).reverse ++ R accum := by
  induction xs generalizing R with
  | nil => simp [gatedSelectedSourceTraceBank, gatedSelectedSourceProfileWord]
  | cons x xs ih =>
    rw [gatedSelectedSourceTraceBank, ih]
    simp [gatedSelectedSourceReverseBank, gatedSelectedSourceProfileWord, GatedSelectedSourceChoice.position,
      List.reverse_append, List.append_assoc]

def gatedSelectedSourceClosedBank (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice) :=
  Function.update (Function.update (Function.update R src []) saved
    ((gatedSelectedSourceWords Li Lk xs).reverse ++ R saved)) accum
    ((gatedSelectedSourceProfileWord Li Lk k base xs).reverse ++ R accum)

theorem gatedSelectedSourceTrace_closed (R : Fin T → List (Fin (A + 4))) (src saved accum : Fin T)
    (hss : src ≠ saved) (hsa : src ≠ accum) (haa : saved ≠ accum)
    (Li Lk k : ℕ) (base : Fin 4 → ℕ) (xs : List GatedSelectedSourceChoice)
    (hraw : R src = gatedSelectedSourceWords Li Lk xs) :
    gatedSelectedSourceTraceBank R src saved accum Li Lk k base xs =
      gatedSelectedSourceClosedBank R src saved accum Li Lk k base xs := by
  funext j
  by_cases hj : j = accum
  · subst j
    simp only [gatedSelectedSourceClosedBank, Function.update_self]
    exact gatedSelectedSourceTrace_output R src saved accum Li Lk k base xs
  · by_cases hs : j = saved
    · subst j
      simp only [gatedSelectedSourceClosedBank, Function.update_of_ne haa, Function.update_self]
      exact gatedSelectedSourceTrace_archive R src saved accum haa Li Lk k base xs
    · by_cases hc : j = src
      · subst j
        simp only [gatedSelectedSourceClosedBank, Function.update_of_ne hsa, Function.update_of_ne hss, Function.update_self]
        exact gatedSelectedSourceTrace_input R src saved accum hss hsa Li Lk k base xs hraw
      · simp only [gatedSelectedSourceClosedBank, Function.update_of_ne hj, Function.update_of_ne hs, Function.update_of_ne hc]
        exact gatedSelectedSourceTrace_keep R src saved accum Li Lk k base xs j hc hs hj

end IntegerMultBounds.MathlibTM2.Routing
