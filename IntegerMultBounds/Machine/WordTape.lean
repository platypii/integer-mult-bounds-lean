import IntegerMultBounds.Machine.Execution

/-! Arbitrary finite-alphabet words placed in a segment of a two-sided tape.
Cells outside the segment may contain other records or control data. -/

namespace IntegerMultBounds.Machine

variable {a : ℕ}

def putWord (f : ℤ → Fin (a + 4)) (p : ℤ) : List (Fin (a + 4)) → ℤ → Fin (a + 4)
  | [] => f
  | x :: xs => Function.update (putWord f (p + 1) xs) p x

theorem putWord_outside (f : ℤ → Fin (a + 4)) (p j : ℤ) (xs : List (Fin (a + 4)))
    (h : j < p ∨ p + xs.length ≤ j) : putWord f p xs j = f j := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    have hj : j ≠ p := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h; omega
    simp only [putWord, Function.update_of_ne hj]
    apply ih
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
    omega

theorem putWord_head (f : ℤ → Fin (a + 4)) (p : ℤ) (x : Fin (a + 4))
    (xs : List (Fin (a + 4))) : putWord f p (x :: xs) p = x := by simp [putWord]

theorem putWord_update_before (f : ℤ → Fin (a + 4)) (p j : ℤ) (x : Fin (a + 4))
    (xs : List (Fin (a + 4))) (h : j < p) :
    putWord (Function.update f j x) p xs = Function.update (putWord f p xs) j x := by
  induction xs generalizing p with
  | nil => rfl
  | cons y xs ih =>
    simp only [putWord, ih (p + 1) (by omega)]
    exact Function.update_comm (β := fun _ : ℤ => Fin (a + 4))
      (show j ≠ p by omega) x y _

theorem putWord_cons (f : ℤ → Fin (a + 4)) (p : ℤ) (x : Fin (a + 4))
    (xs : List (Fin (a + 4))) :
    putWord f p (x :: xs) = putWord (Function.update f p x) (p + 1) xs := by
  rw [putWord_update_before f (p + 1) p x xs (by omega)]
  rfl

theorem putWord_replace_head (f : ℤ → Fin (a + 4)) (p : ℤ) (x y : Fin (a + 4))
    (xs : List (Fin (a + 4))) :
    Function.update (putWord f p (x :: xs)) p y =
      putWord (Function.update f p y) (p + 1) xs := by
  rw [putWord_update_before f (p + 1) p y xs (by omega)]
  simp [putWord]

/-- Adjacent segments can be assembled without assumptions about the background. -/
theorem putWord_append (f : ℤ → Fin (a + 4)) (p : ℤ)
    (xs ys : List (Fin (a + 4))) :
    putWord f p (xs ++ ys) = putWord (putWord f (p + xs.length) ys) p xs := by
  induction xs generalizing p with
  | nil => simp [putWord]
  | cons x xs ih =>
    simp only [List.cons_append, putWord, ih, List.length_cons, Nat.cast_add, Nat.cast_one,
      add_assoc, add_comm]

/-- Appending at the current write head gives the same complete tape as writing
the concatenated word once, including when the background is not blank. -/
theorem putWord_append_forward (f : ℤ → Fin (a + 4)) (p : ℤ)
    (xs ys : List (Fin (a + 4))) :
    putWord (putWord f p xs) (p + xs.length) ys = putWord f p (xs ++ ys) := by
  induction xs generalizing p with
  | nil => simp [putWord]
  | cons x xs ih =>
    simp only [putWord, List.length_cons, Nat.cast_add, Nat.cast_one, List.cons_append]
    rw [putWord_update_before _ _ p x ys (by omega)]
    rw [show p + (xs.length + 1) = (p + 1) + xs.length by omega, ih]

private theorem wordTape_cons_pos (x : Fin (a + 4)) (xs : List (Fin (a + 4)))
    (j : ℤ) (hj : 0 < j) : wordTape (x :: xs) j = wordTape xs (j - 1) := by
  have hn : j.toNat = (j - 1).toNat + 1 := by omega
  simp only [wordTape, show 0 ≤ j by omega, show 0 ≤ j - 1 by omega, ↓reduceIte, hn]
  simp

/-- On a blank background, a placed word has exactly the global blank-tail
semantics required by the end-to-end output specification. -/
theorem putWord_blank (p j : ℤ) (xs : List (Fin (a + 4))) :
    putWord (fun _ => blank) p xs j = wordTape xs (j - p) := by
  induction xs generalizing p with
  | nil => simp [putWord, wordTape]
  | cons x xs ih =>
    by_cases hj : j = p
    · subst j; simp [putWord, wordTape]
    · by_cases hlo : j < p
      · rw [putWord_outside _ _ _ _ (Or.inl hlo)]
        simp [wordTape, not_le.mpr hlo]
      · rw [putWord, Function.update_of_ne hj, ih,
          wordTape_cons_pos x xs (j - p) (by omega)]
        congr 1
        omega

end IntegerMultBounds.Machine
