module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingCoordinateLoop
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedScheduleTrace

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

-- Earlier separate trace helpers: restore from 531cf0a0.
theorem matchingCoordinateTrace_closed (R : Fin T → List (Fin (A + 4))) (rg : Fin 11 → Fin T)
    (hrg : Function.Injective rg) (reverse : Bool) (Li Lk : ℕ) (xs : List (ℕ × ℕ))
    (hinput : R (rg 7) = matchingEntryWords (Li + Lk) xs) :
    matchingCoordinateTraceBank R rg reverse Li Lk xs = matchingCoordinateClosedBank R rg reverse Li Lk xs := by
  let frame := fun x : ℕ × ℕ => matchingEntryWord (A := A) (Li + Lk) x.1 x.2
  let output := fun x : ℕ × ℕ => sourceCoordinateInputRecord (A := A) Li Lk
    (matchingCoordinateInput reverse x.1 x.2).1 (matchingCoordinateInput reverse x.1 x.2).2
  have hi (ys : List (ℕ × ℕ)) : delimitedScheduleInput frame ys = matchingEntryWords (Li + Lk) ys := by
    induction ys with
    | nil => rfl
    | cons y ys ih => simp only [delimitedScheduleInput, matchingEntryWords, frame, ih]
  have ho (ys : List (ℕ × ℕ)) : ys.flatMap output = matchingCoordinateOutput reverse Li Lk ys := by
    induction ys with
    | nil => rfl
    | cons y ys ih => simpa only [List.flatMap_cons, matchingCoordinateOutput, List.map_cons,
        sourceCoordinateInputWords, output] using congrArg (output y ++ ·) ih
  have ht (ys : List (ℕ × ℕ)) (bank : Fin T → List (Fin (A + 4))) :
      matchingCoordinateTraceBank bank rg reverse Li Lk ys =
        delimitedScheduleBank (rg 7) (rg 8) (rg 10) frame (fun x w => (output x).reverse ++ w) ys bank := by
    induction ys generalizing bank with
    | nil => rfl
    | cons y ys ih =>
      simpa only [matchingCoordinateTraceBank, delimitedScheduleBank, matchingCoordinateStepBank,
        delimitedCallAdvanced, hi, frame, output] using
          ih (matchingCoordinateStepBank bank rg reverse Li Lk y.1 y.2 (matchingEntryWords (Li + Lk) ys))
  rw [ht]
  have h := delimitedScheduleBank_prepend (rg 7) (rg 8) (rg 10)
    (hrg.ne (by decide)) (hrg.ne (by decide)) (hrg.ne (by decide)) frame output xs R (by rw [hi]; exact hinput)
  simpa only [hi, ho, matchingCoordinateClosedBank] using h

end IntegerMultBounds.MathlibTM2.Routing
