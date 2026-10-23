module

public import IntegerMultBounds.MathlibTM2.Routing.SourceActivityLoop

/-! Closed final bank for activity extraction, including the entire rewind
archive and the reversed activity word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

def sourceActivityWord (xs : List GatedSelectedSourceChoice) : List (Fin (A + 4)) :=
  xs.map (fun x => bitSymbol x.enabled)

def sourceActivityClosedBank (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (Li Lk : ℕ) (xs : List GatedSelectedSourceChoice) :=
  Function.update (Function.update (Function.update R src []) saved
    ((gatedSelectedSourceWords Li Lk xs).reverse ++ R saved)) dst
    ((sourceActivityWord xs).reverse ++ R dst)

theorem sourceActivityTrace_keep (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (Li Lk : ℕ) (xs : List GatedSelectedSourceChoice)
    (j : Fin T) (hs : j ≠ src) (ha : j ≠ saved) (hd : j ≠ dst) :
    sourceActivityTraceBank R src saved dst Li Lk xs j = R j := by
  induction xs generalizing R with
  | nil => rfl
  | cons x xs ih => rw [sourceActivityTraceBank, ih]; simp [sourceActivityRecordBank, hs, ha, hd]

theorem sourceActivityTrace_input (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (hss : src ≠ saved) (hsd : src ≠ dst) (Li Lk : ℕ) (xs : List GatedSelectedSourceChoice)
    (hraw : R src = gatedSelectedSourceWords Li Lk xs) :
    sourceActivityTraceBank R src saved dst Li Lk xs src = [] := by
  induction xs generalizing R with
  | nil => exact hraw
  | cons x xs ih => apply ih; simp [sourceActivityRecordBank, hss, hsd]

theorem sourceActivityTrace_archive (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (had : saved ≠ dst) (Li Lk : ℕ) (xs : List GatedSelectedSourceChoice) :
    sourceActivityTraceBank R src saved dst Li Lk xs saved =
      (gatedSelectedSourceWords Li Lk xs).reverse ++ R saved := by
  induction xs generalizing R with
  | nil => simp [sourceActivityTraceBank, gatedSelectedSourceWords]
  | cons x xs ih =>
    rw [sourceActivityTraceBank, ih]
    simp [sourceActivityRecordBank, gatedSelectedSourceWords, GatedSelectedSourceChoice.word,
      List.reverse_append, List.append_assoc, had]

theorem sourceActivityTrace_output (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (Li Lk : ℕ) (xs : List GatedSelectedSourceChoice) :
    sourceActivityTraceBank R src saved dst Li Lk xs dst =
      (sourceActivityWord xs).reverse ++ R dst := by
  induction xs generalizing R with
  | nil => simp [sourceActivityTraceBank, sourceActivityWord]
  | cons x xs ih =>
    rw [sourceActivityTraceBank, ih]
    simp [sourceActivityRecordBank, sourceActivityWord, List.append_assoc]

theorem sourceActivityTrace_closed (R : Fin T → List (Fin (A + 4))) (src saved dst : Fin T)
    (hss : src ≠ saved) (hsd : src ≠ dst) (had : saved ≠ dst)
    (Li Lk : ℕ) (xs : List GatedSelectedSourceChoice)
    (hraw : R src = gatedSelectedSourceWords Li Lk xs) :
    sourceActivityTraceBank R src saved dst Li Lk xs = sourceActivityClosedBank R src saved dst Li Lk xs := by
  funext j
  by_cases hd : j = dst
  · subst j
    simp only [sourceActivityClosedBank, Function.update_self]
    exact sourceActivityTrace_output R src saved dst Li Lk xs
  · by_cases ha : j = saved
    · subst j
      simp only [sourceActivityClosedBank, Function.update_of_ne had, Function.update_self]
      exact sourceActivityTrace_archive R src saved dst had Li Lk xs
    · by_cases hs : j = src
      · subst j
        simp only [sourceActivityClosedBank, Function.update_of_ne hsd, Function.update_of_ne hss, Function.update_self]
        exact sourceActivityTrace_input R src saved dst hss hsd Li Lk xs hraw
      · simp only [sourceActivityClosedBank, Function.update_of_ne hd, Function.update_of_ne ha, Function.update_of_ne hs]
        exact sourceActivityTrace_keep R src saved dst Li Lk xs j hs ha hd

end IntegerMultBounds.MathlibTM2.Routing
