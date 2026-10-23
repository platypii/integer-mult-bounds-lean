module

public import IntegerMultBounds.MathlibTM2.Routing.ResidueEntryLoop

/-! The scanner's closed final bank records exactly the input archive andd output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

def residueEntryOutput (L k r : ℕ) (xs : List (ℕ × ℕ)) : List (Fin (A + 4)) :=
  matchingEntryWords L (xs.filter fun x => decide (x.1 % k = r))

def residueEntryClosedBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T)
    (L _Lk k r : ℕ) (xs : List (ℕ × ℕ)) :=
  Function.update (Function.update (Function.update R (rg 14) []) (rg 15)
    ((matchingEntryWords L xs).reverse ++ R (rg 15))) (rg 17)
    ((residueEntryOutput L k r xs).reverse ++ R (rg 17))

theorem residueEntryTrace_keep (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T)
    (L Lk k r : ℕ) (xs : List (ℕ × ℕ)) (j : Fin T)
    (hs : j ≠ rg 14) (ha : j ≠ rg 15) (hd : j ≠ rg 17) :
    residueEntryTraceBank R rg L Lk k r xs j = R j := by
  induction xs generalizing R with
  | nil => rfl
  | cons x xs ih => rw [residueEntryTraceBank, ih]; simp [residueEntryStepBank, hs, ha, hd]

theorem residueEntryTrace_input (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T)
    (hrg : Function.Injective rg) (L Lk k r : ℕ) (xs : List (ℕ × ℕ))
    (hinput : R (rg 14) = matchingEntryWords L xs) :
    residueEntryTraceBank R rg L Lk k r xs (rg 14) = [] := by
  induction xs generalizing R with
  | nil => exact hinput
  | cons x xs ih => apply ih; simp [residueEntryStepBank, hrg.eq_iff]

theorem residueEntryTrace_archive (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T)
    (hrg : Function.Injective rg) (L Lk k r : ℕ) (xs : List (ℕ × ℕ)) :
    residueEntryTraceBank R rg L Lk k r xs (rg 15) =
      (matchingEntryWords L xs).reverse ++ R (rg 15) := by
  induction xs generalizing R with
  | nil => simp [residueEntryTraceBank, matchingEntryWords]
  | cons x xs ih =>
    rw [residueEntryTraceBank, ih]
    simp [residueEntryStepBank, matchingEntryWords, List.reverse_append, List.append_assoc, hrg.eq_iff]

theorem residueEntryTrace_output (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T)
    (L Lk k r : ℕ) (xs : List (ℕ × ℕ)) :
    residueEntryTraceBank R rg L Lk k r xs (rg 17) =
      (residueEntryOutput L k r xs).reverse ++ R (rg 17) := by
  induction xs generalizing R with
  | nil => simp [residueEntryTraceBank, residueEntryOutput, matchingEntryWords]
  | cons x xs ih =>
    rw [residueEntryTraceBank, ih]
    by_cases h : x.1 % k = r <;>
      simp [residueEntryStepBank, residueEntryOutput, residueEntryWord, matchingEntryWords, h, List.append_assoc]

theorem residueEntryTrace_closed (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T)
    (hrg : Function.Injective rg) (L Lk k r : ℕ) (xs : List (ℕ × ℕ))
    (hinput : R (rg 14) = matchingEntryWords L xs) :
    residueEntryTraceBank R rg L Lk k r xs = residueEntryClosedBank R rg L Lk k r xs := by
  funext j
  by_cases hd : j = rg 17
  · subst j
    simp only [residueEntryClosedBank, Function.update_self]
    exact residueEntryTrace_output R rg L Lk k r xs
  by_cases ha : j = rg 15
  · subst j
    simp only [residueEntryClosedBank, Function.update_of_ne (hrg.ne (by decide : (15 : Fin 18) ≠ 17)), Function.update_self]
    exact residueEntryTrace_archive R rg hrg L Lk k r xs
  by_cases hs : j = rg 14
  · subst j
    simp only [residueEntryClosedBank, Function.update_of_ne (hrg.ne (by decide : (14 : Fin 18) ≠ 17)),
      Function.update_of_ne (hrg.ne (by decide : (14 : Fin 18) ≠ 15)), Function.update_self]
    exact residueEntryTrace_input R rg hrg L Lk k r xs hinput
  · simp only [residueEntryClosedBank, Function.update_of_ne hd, Function.update_of_ne ha, Function.update_of_ne hs]
    exact residueEntryTrace_keep R rg L Lk k r xs j hs ha hd

end IntegerMultBounds.MathlibTM2.Routing
