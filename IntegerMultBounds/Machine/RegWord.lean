import IntegerMultBounds.Machine.Registers
import IntegerMultBounds.Machine.TwosComplement
import IntegerMultBounds.Machine.FixedMul

/-! Registers as fixed-width words: a ruler copy of `w` cells from a register
gives its canonical word padded with zeros to width `w`, and for values below
`2^(w-1)` that word has the register's value as its signed value. -/

namespace IntegerMultBounds.Machine.RegWord

open Registers (canon canon_value canon_canonical reg)
open CopyCells (cells zeroFill)
open TwosComplement (signed)

variable {a : ℕ}

/-- The canonical word of `n` padded with zeros to width `w`. -/
def padTo (n w : ℕ) : List Bool := canon n ++ List.replicate (w - (canon n).length) false

theorem padTo_length (n w : ℕ) (h : (canon n).length ≤ w) : (padTo n w).length = w := by
  simp [padTo]; omega

theorem cells_reg (n w : ℕ) (h : (canon n).length ≤ w) :
    cells (reg (a := a) n) 0 w = (padTo n w).map bitSymbol := by
  have hw : w = (canon n).length + (w - (canon n).length) := by omega
  conv_lhs => rw [hw]
  rw [FixedMul.cells_add, show reg (a := a) n = putWord (fun _ => blank) 0 ((canon n).map bitSymbol) from rfl]
  have h1 := CopyCells.cells_putWord (fun _ => (blank : Fin (a + 4))) 0 (canon n)
  rw [h1, zero_add]
  have h2 : cells (putWord (fun _ => (blank : Fin (a + 4))) 0 ((canon n).map bitSymbol)) ((canon n).length : ℤ)
      (w - (canon n).length) = List.replicate (w - (canon n).length) (bitSymbol false) := by
    rw [FixedMul.cells_of_blank _ _ _ (fun k => putWord_outside _ _ _ _ (Or.inr (by simp)))]
    simp [List.map_replicate]
  rw [h2]
  simp [padTo, List.map_append, List.map_replicate]

theorem canon_length_lt (n w : ℕ) (hw : 1 ≤ w) (h : n < 2 ^ (w - 1)) : (canon n).length < w := by
  have hc := GrowingCounterData.canonical_width (canon n) (canon_canonical n)
  rw [canon_value] at hc
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp [canon, GrowingCounterData.advance]; omega
  · have := Nat.log2_lt (by omega : n ≠ 0) |>.mpr h
    omega

theorem value_padTo (n w : ℕ) : Counter.value (padTo n w) = n := by
  rw [padTo, Registers.value_padding, canon_value]

theorem signed_padTo (n w : ℕ) (hw : 1 ≤ w) (h : n < 2 ^ (w - 1)) : signed (padTo n w) = n := by
  have hl := canon_length_lt n w hw h
  unfold signed
  have hlast : (padTo n w).getLastD false = false := by
    unfold padTo
    obtain ⟨k, hk⟩ : ∃ k, w - (canon n).length = k + 1 := ⟨w - (canon n).length - 1, by omega⟩
    rw [hk, List.replicate_succ', ← List.append_assoc, List.getLastD_eq_getLast?, List.getLast?_append]
    simp
  rw [hlast, value_padTo]
  simp

end IntegerMultBounds.Machine.RegWord
