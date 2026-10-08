import IntegerMultBounds.Machine.WordTape

/-! Fixed-radix digits in the extra portion of the machine alphabet. The four
reserved symbols remain available, and every data digit is distinct from blank. -/

namespace IntegerMultBounds.Machine.RadixDigits

variable {q : ℕ}

def digitSymbol (x : Fin q) : Fin (q + 4) := ⟨x.val + 4, by omega⟩

def readDigit (s : Fin (q + 4)) : Option (Fin q) :=
  if h : 4 ≤ s.val then some ⟨s.val - 4, by omega⟩ else none

@[simp] theorem readDigit_symbol (x : Fin q) : readDigit (digitSymbol x) = some x := by
  simp only [readDigit,digitSymbol,show 4 ≤ x.val + 4 by omega]
  congr 1

@[simp] theorem readDigit_blank : readDigit (blank : Fin (q + 4)) = none := by
  simp [readDigit,blank]

/-- The numerical value of a least-significant-first word. -/
def value : List (Fin q) → ℕ
  | [] => 0
  | x :: xs => x.val + q * value xs

/-- Every fixed-width word is a canonical residue modulo its radix power. -/
theorem value_lt (_hq : 2 ≤ q) (xs : List (Fin q)) : value xs < q ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih =>
    have hx := x.isLt
    simp only [value,List.length_cons,pow_succ]
    nlinarith

end IntegerMultBounds.Machine.RadixDigits
