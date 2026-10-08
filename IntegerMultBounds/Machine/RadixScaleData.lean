import IntegerMultBounds.Machine.RadixDigits

/-! Fixed-natural-coefficient scaling by a bounded-carry radix transducer.
The state bound depends on the fixed coefficient, never on word length. -/

namespace IntegerMultBounds.Machine.RadixScaleData

open RadixDigits
variable {q coefficient : ℕ} [NeZero q]

private theorem radix_pos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)

def digit (c : Fin (coefficient + 1)) (x : Fin q) : Fin q :=
  ⟨(coefficient * x.val + c.val) % q, Nat.mod_lt _ radix_pos⟩

private theorem carry_lt (c : Fin (coefficient + 1)) (x : Fin q) :
    (coefficient * x.val + c.val) / q < coefficient + 1 := by
  apply (Nat.div_lt_iff_lt_mul radix_pos).mpr
  have hm := Nat.mul_le_mul_left coefficient (Nat.succ_le_of_lt x.isLt)
  have hc := c.isLt
  have hq : 0 < q := radix_pos
  nlinarith

def carry (c : Fin (coefficient + 1)) (x : Fin q) : Fin (coefficient + 1) :=
  ⟨(coefficient * x.val + c.val) / q, carry_lt c x⟩

theorem column (c : Fin (coefficient + 1)) (x : Fin q) :
    (digit c x).val + q * (carry c x).val = coefficient * x.val + c.val :=
  Nat.mod_add_div _ _

def digits : Fin (coefficient + 1) → List (Fin q) → List (Fin q)
  | _, [] => []
  | c, x :: xs => digit c x :: digits (carry c x) xs

def overflow : Fin (coefficient + 1) → List (Fin q) → Fin (coefficient + 1)
  | c, [] => c
  | c, x :: xs => overflow (carry c x) xs

@[simp] theorem digits_length (c : Fin (coefficient + 1)) (xs : List (Fin q)) :
    (digits c xs).length = xs.length := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [digits,List.length_cons,ih]

theorem digits_value (c : Fin (coefficient + 1)) (xs : List (Fin q)) :
    value (digits c xs) + q ^ xs.length * (overflow c xs).val = coefficient * value xs + c.val := by
  induction xs generalizing c with
  | nil => simp [digits,overflow,value]
  | cons x xs ih =>
    have hc := column c x
    have hi := ih (carry c x)
    simp only [digits,overflow,value,List.length_cons,pow_succ]
    nlinarith

/-- Exact word-width modular multiplication, with an optional incoming carry. -/
theorem digits_value_mod (hq : 2 ≤ q) (c : Fin (coefficient + 1)) (xs : List (Fin q)) :
    value (digits c xs) = (coefficient * value xs + c.val) % q ^ xs.length := by
  have hv := digits_value c xs
  have hl : value (digits c xs) < q ^ xs.length := by
    rw [← digits_length c xs]
    exact value_lt hq _
  rw [← hv,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hl]

end IntegerMultBounds.Machine.RadixScaleData
