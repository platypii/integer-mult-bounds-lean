module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateLoop

/-! The scanner's closed final bank records exactly the input archive and reversed output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

def matchingCoordinateOutput (reverse : Bool) (Li Lk : ℕ) (xs : List (ℕ × ℕ)) : List (Fin (A + 4)) :=
  sourceCoordinateInputWords Li Lk (xs.map fun x => matchingCoordinateInput reverse x.1 x.2)

def matchingCoordinateClosedBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T)
    (reverse : Bool) (Li Lk : ℕ) (xs : List (ℕ × ℕ)) :=
  Function.update (Function.update (Function.update R (rg 7) []) (rg 8)
    ((matchingEntryWords (Li + Lk) xs).reverse ++ R (rg 8))) (rg 10)
    ((matchingCoordinateOutput reverse Li Lk xs).reverse ++ R (rg 10))

theorem matchingCoordinateTrace_keep (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T)
    (reverse : Bool) (Li Lk : ℕ) (xs : List (ℕ × ℕ)) (j : Fin T)
    (hs : j ≠ rg 7) (ha : j ≠ rg 8) (hd : j ≠ rg 10) :
    matchingCoordinateTraceBank R rg reverse Li Lk xs j = R j := by
  induction xs generalizing R with
  | nil => rfl
  | cons x xs ih => rw [matchingCoordinateTraceBank, ih]; simp [matchingCoordinateStepBank, hs, ha, hd]

theorem matchingCoordinateTrace_input (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T)
    (hrg : Function.Injective rg) (reverse : Bool) (Li Lk : ℕ) (xs : List (ℕ × ℕ))
    (hinput : R (rg 7) = matchingEntryWords (Li + Lk) xs) :
    matchingCoordinateTraceBank R rg reverse Li Lk xs (rg 7) = [] := by
  induction xs generalizing R with
  | nil => exact hinput
  | cons x xs ih => apply ih; simp [matchingCoordinateStepBank, hrg.eq_iff]

theorem matchingCoordinateTrace_archive (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T)
    (hrg : Function.Injective rg) (reverse : Bool) (Li Lk : ℕ) (xs : List (ℕ × ℕ)) :
    matchingCoordinateTraceBank R rg reverse Li Lk xs (rg 8) =
      (matchingEntryWords (Li + Lk) xs).reverse ++ R (rg 8) := by
  induction xs generalizing R with
  | nil => simp [matchingCoordinateTraceBank, matchingEntryWords]
  | cons x xs ih =>
    rw [matchingCoordinateTraceBank, ih]
    simp [matchingCoordinateStepBank, matchingEntryWords, List.reverse_append, List.append_assoc, hrg.eq_iff]

theorem matchingCoordinateTrace_output (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T)
    (reverse : Bool) (Li Lk : ℕ) (xs : List (ℕ × ℕ)) :
    matchingCoordinateTraceBank R rg reverse Li Lk xs (rg 10) =
      (matchingCoordinateOutput reverse Li Lk xs).reverse ++ R (rg 10) := by
  induction xs generalizing R with
  | nil => simp [matchingCoordinateTraceBank, matchingCoordinateOutput, sourceCoordinateInputWords]
  | cons x xs ih =>
    rw [matchingCoordinateTraceBank, ih]
    simp [matchingCoordinateStepBank, matchingCoordinateOutput, sourceCoordinateInputWords, List.append_assoc]

theorem matchingCoordinateTrace_closed (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T)
    (hrg : Function.Injective rg) (reverse : Bool) (Li Lk : ℕ) (xs : List (ℕ × ℕ))
    (hinput : R (rg 7) = matchingEntryWords (Li + Lk) xs) :
    matchingCoordinateTraceBank R rg reverse Li Lk xs = matchingCoordinateClosedBank R rg reverse Li Lk xs := by
  funext j
  by_cases hd : j = rg 10
  · subst j
    simp only [matchingCoordinateClosedBank, Function.update_self]
    exact matchingCoordinateTrace_output R rg reverse Li Lk xs
  by_cases ha : j = rg 8
  · subst j
    simp only [matchingCoordinateClosedBank, Function.update_of_ne (hrg.ne (by decide : (8 : Fin 11) ≠ 10)), Function.update_self]
    exact matchingCoordinateTrace_archive R rg hrg reverse Li Lk xs
  by_cases hs : j = rg 7
  · subst j
    simp only [matchingCoordinateClosedBank, Function.update_of_ne (hrg.ne (by decide : (7 : Fin 11) ≠ 10)),
      Function.update_of_ne (hrg.ne (by decide : (7 : Fin 11) ≠ 8)), Function.update_self]
    exact matchingCoordinateTrace_input R rg hrg reverse Li Lk xs hinput
  · simp only [matchingCoordinateClosedBank, Function.update_of_ne hd, Function.update_of_ne ha, Function.update_of_ne hs]
    exact matchingCoordinateTrace_keep R rg reverse Li Lk xs j hs ha hd

end IntegerMultBounds.MathlibTM2.Routing
