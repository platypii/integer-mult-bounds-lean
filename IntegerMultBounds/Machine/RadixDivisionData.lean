import IntegerMultBounds.Machine.RadixDigits
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Fixed-denominator modular division by a digit transducer. The carry is a
member of Fin d, independent of input width. One output digit solves the local
congruence modulo the fixed prime radix, and exact arithmetic telescopes. -/

namespace IntegerMultBounds.Machine.RadixDivisionData

open RadixDigits
variable {q d : ℕ} [Fact q.Prime]

/-- A fixed finite lookup from incoming carry and source digit to output digit. -/
def digit (c : Fin d) (x : Fin q) : Fin q :=
  ⟨((d : ZMod q)⁻¹ * ((x.val : ZMod q) - (c.val : ZMod q))).val, ZMod.val_lt _⟩

private theorem carry_lt (c : Fin d) (x : Fin q) :
    (d * (digit c x).val + c.val) / q < d := by
  have hq := (Fact.out : q.Prime).pos
  apply (Nat.div_lt_iff_lt_mul hq).mpr
  have hm := Nat.mul_le_mul_left d (Nat.succ_le_of_lt (digit c x).isLt)
  have hc := c.isLt
  nlinarith

def carry (c : Fin d) (x : Fin q) : Fin d :=
  ⟨(d * (digit c x).val + c.val) / q, carry_lt c x⟩

/-- Exactly the current digit is the remainder; division never truncates a
negative carry. The next carry stays in the fixed d-element state set. -/
theorem column (hdpos : 0 < d) (hdq : d < q) (c : Fin d) (x : Fin q) :
    d * (digit c x).val + c.val = x.val + q * (carry c x).val := by
  have hd : (d : ZMod q) ≠ 0 := by
    intro h
    have hh := (ZMod.natCast_eq_zero_iff d q).mp h
    have hle := Nat.le_of_dvd hdpos hh
    omega
  have hv : ((digit c x).val : ZMod q) =
      (d : ZMod q)⁻¹ * ((x.val : ZMod q) - (c.val : ZMod q)) :=
    ZMod.natCast_zmod_val _
  have hz : ((d * (digit c x).val + c.val : ℕ) : ZMod q) = (x.val : ZMod q) := by
    push_cast
    rw [hv,← mul_assoc,mul_inv_cancel₀ hd,one_mul,sub_add_cancel]
  have hm := (ZMod.natCast_eq_natCast_iff' _ _ q).mp hz
  rw [Nat.mod_eq_of_lt x.isLt] at hm
  have hh := Nat.mod_add_div (d * (digit c x).val + c.val) q
  rw [hm] at hh
  exact hh.symm

def digits : Fin d → List (Fin q) → List (Fin q)
  | _, [] => []
  | c, x :: xs => digit c x :: digits (carry c x) xs

def overflow : Fin d → List (Fin q) → Fin d
  | c, [] => c
  | c, x :: xs => overflow (carry c x) xs

@[simp] theorem digits_length (c : Fin d) (xs : List (Fin q)) :
    (digits c xs).length = xs.length := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [digits,List.length_cons,ih]

/-- Exact integer identity, including incoming and outgoing finite carry. -/
theorem digits_value (hdpos : 0 < d) (hdq : d < q) (c : Fin d) (xs : List (Fin q)) :
    d * value (digits c xs) + c.val = value xs + q ^ xs.length * (overflow c xs).val := by
  induction xs generalizing c with
  | nil => simp [digits,overflow,value]
  | cons x xs ih =>
    have hc := column hdpos hdq c x
    have hi := ih (carry c x)
    simp only [digits,overflow,value,List.length_cons,pow_succ]
    nlinarith

/-- The output divides the input modulo the exact word modulus. -/
theorem divides_mod (hdpos : 0 < d) (hdq : d < q) (xs : List (Fin q)) :
    (d * value (digits ⟨0,hdpos⟩ xs)) % q ^ xs.length = value xs := by
  have hv := digits_value hdpos hdq ⟨0,hdpos⟩ xs
  simp only [Nat.add_zero] at hv
  rw [hv,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (value_lt (Fact.out : q.Prime).two_le xs)]

end IntegerMultBounds.Machine.RadixDivisionData
