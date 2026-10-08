import IntegerMultBounds.Machine.WordTape

/-! Exact local views into concatenated raw tape words. These representation
lemmas support repeated stream routines without extra reads or writes; runtime
claims belong to the literal programs that consume the views. -/

namespace IntegerMultBounds.Machine.WordSegments

variable {a : ℕ}

theorem get (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List (Fin (a+4)))
    (i : ℕ) (hi : i < xs.length) : putWord f p xs (p+i) = xs[i] := by
  induction xs generalizing p i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [putWord]
    | succ i =>
      rw [putWord,Function.update_of_ne (by omega)]
      simpa only [List.getElem_cons_succ,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm]
        using ih (p+1) i (by simpa using hi)

/-- Rewriting an already matching segment leaves the entire tape identical. -/
theorem of_agrees (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List (Fin (a+4)))
    (h : ∀ i : ℕ, ∀ hi : i < xs.length, f (p+i) = xs[i]) : putWord f p xs = f := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    have ht : ∀ i : ℕ, ∀ hi : i < xs.length, f (p+1+i) = xs[i] := by
      intro i hi
      have hh := h (i+1) (by simpa using hi)
      change f (p+((i+1 : ℕ) : ℤ)) = xs[i] at hh
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hh
    rw [putWord,ih (p+1) ht]
    apply Function.update_eq_self_iff.mpr
    have hh := h 0 (by simp)
    change f (p+0) = x at hh
    simpa using hh.symm

/-- The middle word of a placed concatenation is already present at its exact
length-offset origin, independently of the tape background. -/
theorem middle (f : ℤ → Fin (a+4)) (p : ℤ) (left mid right : List (Fin (a+4))) :
    putWord (putWord f p (left++mid++right)) (p+left.length) mid =
      putWord f p (left++mid++right) := by
  apply of_agrees
  intro i hi
  have hj : left.length+i < (left++mid++right).length := by simp; omega
  have hh := get f p (left++mid++right) (left.length+i) hj
  simpa [List.getElem_append,hi,show ¬left.length+i < left.length by omega,
    show left.length+i < left.length+mid.length by omega,Nat.cast_add,add_assoc] using hh

end IntegerMultBounds.Machine.WordSegments
