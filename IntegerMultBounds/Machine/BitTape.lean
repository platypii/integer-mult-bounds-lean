import IntegerMultBounds.Machine.Execution

/-! Finite bit segments on otherwise arbitrary tapes. Writing a segment preserves
every cell outside it; this representation does not assume blank spectators. -/

namespace IntegerMultBounds.Machine

def putBits (f : ℤ → Fin 4) (p : ℤ) : List Bool → ℤ → Fin 4
  | [] => f
  | b :: bs => Function.update (putBits f (p + 1) bs) p (bitSymbol b)

theorem putBits_outside (f : ℤ → Fin 4) (p j : ℤ) (bs : List Bool)
    (h : j < p ∨ p + bs.length ≤ j) : putBits f p bs j = f j := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
    have hj : j ≠ p := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h; omega
    simp only [putBits, Function.update_of_ne hj]
    apply ih
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
    omega

theorem putBits_head (f : ℤ → Fin 4) (p : ℤ) (b : Bool) (bs : List Bool) :
    putBits f p (b :: bs) p = bitSymbol b := by simp [putBits]

/-- Updating a cell before a bit segment commutes with writing that segment. -/
theorem putBits_update_before (f : ℤ → Fin 4) (p j : ℤ) (x : Fin 4)
    (bs : List Bool) (h : j < p) :
    putBits (Function.update f j x) p bs = Function.update (putBits f p bs) j x := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
    simp only [putBits, ih (p + 1) (by omega)]
    exact Function.update_comm (β := fun _ : ℤ => Fin 4)
      (show j ≠ p by omega) x (bitSymbol b) _

theorem putBits_cons (f : ℤ → Fin 4) (p : ℤ) (b : Bool) (bs : List Bool) :
    putBits f p (b :: bs) = putBits (Function.update f p (bitSymbol b)) (p + 1) bs := by
  rw [putBits_update_before f (p + 1) p (bitSymbol b) bs (by omega)]
  rfl

/-- Every represented digit is distinct from the segment's boundary marker. -/
theorem putBits_ne_separator (f : ℤ → Fin 4) (p j : ℤ) (bs : List Bool)
    (hlo : p ≤ j) (hhi : j < p + bs.length) : putBits f p bs j ≠ separator := by
  induction bs generalizing p with
  | nil => simp at hhi; omega
  | cons b bs ih =>
    by_cases hj : j = p
    · subst j
      rw [putBits_head]
      cases b <;> decide
    · simp only [putBits, Function.update_of_ne hj]
      apply ih <;> simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hhi <;> omega

end IntegerMultBounds.Machine
