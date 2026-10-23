module

public import IntegerMultBounds.MathlibTM2.Routing.ResidueEntryLoop
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedScheduleTrace

/-! The scanner's closed final bank records exactly the input archive and reversed output. -/

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

-- Earlier separate trace helpers: restore from 531cf0a0.
theorem residueEntryTrace_closed (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T)
    (hrg : Function.Injective rg) (L Lk k r : ℕ) (xs : List (ℕ × ℕ))
    (hinput : R (rg 14) = matchingEntryWords L xs) :
    residueEntryTraceBank R rg L Lk k r xs = residueEntryClosedBank R rg L Lk k r xs := by
  let frame := fun x : ℕ × ℕ => matchingEntryWord (A := A) L x.1 x.2
  let output := fun x : ℕ × ℕ => residueEntryWord (A := A) L x.1 x.2 k r
  have hi (ys : List (ℕ × ℕ)) : delimitedScheduleInput frame ys = matchingEntryWords L ys := by
    induction ys with
    | nil => rfl
    | cons y ys ih => simp only [delimitedScheduleInput, matchingEntryWords, frame, ih]
  have ho (ys : List (ℕ × ℕ)) : ys.flatMap output = residueEntryOutput L k r ys := by
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      dsimp only [residueEntryOutput] at ih ⊢
      dsimp only [output, residueEntryWord] at ih
      by_cases h : y.1 % k = r <;>
        simp [List.flatMap_cons, output, residueEntryWord, h, matchingEntryWords, ih]
  have ht (ys : List (ℕ × ℕ)) (bank : Fin T → List (Fin (A + 4))) :
      residueEntryTraceBank bank rg L Lk k r ys =
        delimitedScheduleBank (rg 14) (rg 15) (rg 17) frame (fun x w => (output x).reverse ++ w) ys bank := by
    induction ys generalizing bank with
    | nil => rfl
    | cons y ys ih =>
      simpa only [residueEntryTraceBank, delimitedScheduleBank, residueEntryStepBank,
        delimitedCallAdvanced, hi, frame, output] using
          ih (residueEntryStepBank bank rg L Lk y.1 y.2 k r (matchingEntryWords L ys))
  rw [ht]
  have h := delimitedScheduleBank_prepend (rg 14) (rg 15) (rg 17)
    (hrg.ne (by decide)) (hrg.ne (by decide)) (hrg.ne (by decide)) frame output xs R (by rw [hi]; exact hinput)
  simpa only [hi, ho, residueEntryClosedBank] using h

end IntegerMultBounds.MathlibTM2.Routing
