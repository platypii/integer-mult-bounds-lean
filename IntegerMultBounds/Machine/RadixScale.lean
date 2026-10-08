import IntegerMultBounds.Machine.RadixScaleData
import IntegerMultBounds.Machine.RadixUnary

/-! Literal fixed-coefficient modular scaling. The two-tape machine has exactly
coefficient+1 finite carry states and takes one transition per source digit.
The radix and coefficient are fixed independently of the input width. -/

namespace IntegerMultBounds.Machine.RadixScale

open RadixDigits RadixScaleData
variable {q coefficient : ℕ} [NeZero q]

def table : RadixUnary.Table q (coefficient + 1) := fun c x => (carry c x,digit c x)

def program (q coefficient : ℕ) [NeZero q] : Program 2 (coefficient + 1) q :=
  RadixUnary.program q (coefficient + 1) ⟨0,Nat.zero_lt_succ _⟩ table

abbrev cfg := @RadixUnary.cfg

theorem outputs_eq (c : Fin (coefficient + 1)) (xs : List (Fin q)) :
    RadixUnary.outputs table c xs = digits c xs := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [RadixUnary.outputs,table,digits,ih]

theorem finalState_eq (c : Fin (coefficient + 1)) (xs : List (Fin q)) :
    RadixUnary.finalState table c xs = overflow c xs := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [RadixUnary.finalState,table,overflow,ih]

/-- Literal runtime and halt, with arbitrary source and output backgrounds. -/
theorem scale_exact (c : Fin (coefficient + 1)) (xs : List (Fin q))
    (source out : ℤ → Fin (q + 4)) (p r : ℤ) (hf : source (p + xs.length) = blank) :
    run (program q coefficient) xs.length
      (cfg (putWord source p (xs.map digitSymbol)) out p r c) =
      some (cfg (putWord source p (xs.map digitSymbol))
        (putWord out r ((digits c xs).map digitSymbol))
        (p + xs.length) (r + xs.length) (overflow c xs)) ∧
    step (program q coefficient)
      (cfg (putWord source p (xs.map digitSymbol))
        (putWord out r ((digits c xs).map digitSymbol))
        (p + xs.length) (r + xs.length) (overflow c xs)) = none := by
  simpa only [program,cfg,outputs_eq,finalState_eq] using
    RadixUnary.exact_run (⟨0,Nat.zero_lt_succ _⟩ : Fin (coefficient + 1)) c table xs source out p r
      (by rw [hf,readDigit_blank])

/-- Exact width cost, with the actual modular arithmetic in the postcondition. -/
theorem scale_hoare (hq : 2 ≤ q) (xs : List (Fin q))
    (source out : ℤ → Fin (q + 4)) (p r : ℤ) (hf : source (p + xs.length) = blank) :
    HoareTime (program q coefficient)
      (fun v => v = (cfg (putWord source p (xs.map digitSymbol)) out p r
        (⟨0,Nat.zero_lt_succ _⟩ : Fin (coefficient + 1))).tapes)
      (fun v => ∃ result : List (Fin q),
        value result = (coefficient * value xs) % q ^ xs.length ∧ result.length = xs.length ∧
        v = (cfg (putWord source p (xs.map digitSymbol)) (putWord out r (result.map digitSymbol))
          (p + xs.length) (r + xs.length) (⟨0,Nat.zero_lt_succ _⟩ : Fin (coefficient + 1))).tapes)
      xs.length := by
  rintro v rfl
  obtain ⟨hr,hh⟩ := scale_exact (⟨0,Nat.zero_lt_succ _⟩ : Fin (coefficient + 1)) xs source out p r hf
  refine ⟨_,_,le_rfl,hr,hh,digits ⟨0,Nat.zero_lt_succ _⟩ xs,?_,digits_length _ _,rfl⟩
  simpa only [Nat.add_zero] using digits_value_mod hq (⟨0,Nat.zero_lt_succ _⟩ : Fin (coefficient + 1)) xs

/-- Blank-output execution exposes the complete word and final finite carry. -/
theorem scale_to_blank (hq : 2 ≤ q) (xs : List (Fin q)) :
    let result := digits (⟨0,Nat.zero_lt_succ _⟩ : Fin (coefficient + 1)) xs
    let last := overflow (⟨0,Nat.zero_lt_succ _⟩ : Fin (coefficient + 1)) xs
    value result = (coefficient * value xs) % q ^ xs.length ∧
    value result + q ^ xs.length * last.val = coefficient * value xs ∧
    result.length = xs.length ∧
    run (program q coefficient) xs.length
      (cfg (wordTape (xs.map digitSymbol)) (fun _ => blank) 0 0 (⟨0,Nat.zero_lt_succ _⟩ : Fin (coefficient + 1))) =
      some (cfg (wordTape (xs.map digitSymbol)) (wordTape (result.map digitSymbol)) xs.length xs.length last) ∧
    step (program q coefficient)
      (cfg (wordTape (xs.map digitSymbol)) (wordTape (result.map digitSymbol)) xs.length xs.length last) = none := by
  refine ⟨?_,?_,digits_length _ _,?_⟩
  · simpa only [Nat.add_zero] using digits_value_mod hq (⟨0,Nat.zero_lt_succ _⟩ : Fin (coefficient + 1)) xs
  · simpa only [Nat.add_zero] using digits_value (⟨0,Nat.zero_lt_succ _⟩ : Fin (coefficient + 1)) xs
  · simpa only [program,cfg,outputs_eq,finalState_eq] using
      RadixUnary.to_blank (⟨0,Nat.zero_lt_succ _⟩ : Fin (coefficient + 1)) table xs

end IntegerMultBounds.Machine.RadixScale
