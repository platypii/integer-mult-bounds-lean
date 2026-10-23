module

public import IntegerMultBounds.MathlibTM2.Routing.SourceCoordinateLoop

/-! Closed final bank for coordinate compilation, including the entire rewind
archive and the reversed canonical record stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

def sourceCoordinateClosedBank (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (Li Lk low high k : ℕ) (xs : List (ℕ × Bool)) :=
  Function.update (Function.update (Function.update R src []) saved
    ((sourceCoordinateInputWords Li Lk xs).reverse ++ R saved)) dst
    ((sourceCoordinateOutputWords Li Lk low high k xs).reverse ++ R dst)

theorem sourceCoordinateTrace_keep (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (Li Lk low high k : ℕ) (xs : List (ℕ × Bool))
    (j : Fin T) (hs : j ≠ src) (ha : j ≠ saved) (hd : j ≠ dst) :
    sourceCoordinateTraceBank R src saved dst Li Lk low high k xs j = R j := by
  induction xs generalizing R with
  | nil => rfl
  | cons x xs ih => rw [sourceCoordinateTraceBank, ih]; simp [sourceCoordinateReverseBank, hs, ha, hd]

theorem sourceCoordinateTrace_input (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (hss : src ≠ saved) (hsd : src ≠ dst) (Li Lk low high k : ℕ) (xs : List (ℕ × Bool))
    (hraw : R src = sourceCoordinateInputWords Li Lk xs) :
    sourceCoordinateTraceBank R src saved dst Li Lk low high k xs src = [] := by
  induction xs generalizing R with
  | nil => exact hraw
  | cons x xs ih => apply ih; simp [sourceCoordinateReverseBank, hss, hsd]

theorem sourceCoordinateTrace_archive (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (had : saved ≠ dst) (Li Lk low high k : ℕ) (xs : List (ℕ × Bool)) :
    sourceCoordinateTraceBank R src saved dst Li Lk low high k xs saved =
      (sourceCoordinateInputWords Li Lk xs).reverse ++ R saved := by
  induction xs generalizing R with
  | nil => simp [sourceCoordinateTraceBank, sourceCoordinateInputWords]
  | cons x xs ih =>
    rw [sourceCoordinateTraceBank, ih]
    simp [sourceCoordinateReverseBank, sourceCoordinateInputWords,
      List.reverse_append, List.append_assoc, had]

theorem sourceCoordinateTrace_output (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (Li Lk low high k : ℕ) (xs : List (ℕ × Bool)) :
    sourceCoordinateTraceBank R src saved dst Li Lk low high k xs dst =
      (sourceCoordinateOutputWords Li Lk low high k xs).reverse ++ R dst := by
  induction xs generalizing R with
  | nil => simp [sourceCoordinateTraceBank, sourceCoordinateOutputWords, gatedSelectedSourceWords]
  | cons x xs ih =>
    rw [sourceCoordinateTraceBank, ih]
    simp [sourceCoordinateReverseBank, sourceCoordinateOutputWords, gatedSelectedSourceWords, List.append_assoc]

theorem sourceCoordinateTrace_closed (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (hss : src ≠ saved) (hsd : src ≠ dst) (had : saved ≠ dst)
    (Li Lk low high k : ℕ) (xs : List (ℕ × Bool))
    (hraw : R src = sourceCoordinateInputWords Li Lk xs) :
    sourceCoordinateTraceBank R src saved dst Li Lk low high k xs = sourceCoordinateClosedBank R src saved dst Li Lk low high k xs := by
  funext j
  by_cases hd : j = dst
  · subst j
    simp only [sourceCoordinateClosedBank, Function.update_self]
    exact sourceCoordinateTrace_output R src saved dst Li Lk low high k xs
  · by_cases ha : j = saved
    · subst j
      simp only [sourceCoordinateClosedBank, Function.update_of_ne had, Function.update_self]
      exact sourceCoordinateTrace_archive R src saved dst had Li Lk low high k xs
    · by_cases hs : j = src
      · subst j
        simp only [sourceCoordinateClosedBank, Function.update_of_ne hsd, Function.update_of_ne hss, Function.update_self]
        exact sourceCoordinateTrace_input R src saved dst hss hsd Li Lk low high k xs hraw
      · simp only [sourceCoordinateClosedBank, Function.update_of_ne hd, Function.update_of_ne ha, Function.update_of_ne hs]
        exact sourceCoordinateTrace_keep R src saved dst Li Lk low high k xs j hs ha hd

end IntegerMultBounds.MathlibTM2.Routing
