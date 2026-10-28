module

public import IntegerMultBounds.NLogN.IntervalRunMask

/-! Prefix algebra for a cursor-based interval run producer. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.IntervalRunMask

def cursor (start : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => start
  | (_,hi)::xs => cursor hi xs

def prefixRuns (start : ℕ) : List (ℕ × ℕ) → List (Bool × ℕ)
  | [] => []
  | (lo,hi)::xs => (false,lo-start)::(true,hi-lo)::prefixRuns hi xs

theorem cursor_append (start : ℕ) (xs ys : List (ℕ × ℕ)) :
    cursor start (xs++ys) = cursor (cursor start xs) ys := by
  induction xs generalizing start with
  | nil => rfl
  | cons r xs ih => exact ih r.2

theorem prefixRuns_append (start : ℕ) (xs ys : List (ℕ × ℕ)) :
    prefixRuns start (xs++ys) = prefixRuns start xs++prefixRuns (cursor start xs) ys := by
  induction xs generalizing start with
  | nil => rfl
  | cons r xs ih => simp [prefixRuns,cursor,ih]

theorem runs_eq_prefix (start stop : ℕ) (xs : List (ℕ × ℕ)) :
    runs start stop xs = prefixRuns start xs++[(false,stop-cursor start xs)] := by
  induction xs generalizing start with
  | nil => rfl
  | cons r xs ih => simp [runs,prefixRuns,cursor,ih]

end IntegerMultBounds.NLogN.IntervalRunMask
