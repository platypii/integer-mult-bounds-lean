import IntegerMultBounds.Machine.DoubleClockReverseCopy
import IntegerMultBounds.Machine.ElementaryMultiplyCore
import IntegerMultBounds.Machine.Registers

/-! Exact output serialization for the elementary multiplier. Reverse copying
the full two-input-width window appends high zeros to the little-endian
accumulator before reversal, producing the required padded MSB product word. -/
namespace IntegerMultBounds.Machine.ElementaryMultiplyOutputData
variable {a : ℕ}
open DoubleClockReverseCopy (copied readBit)

/-- The literal reverse-copy recursion reads the cell p-i at output index i. -/
theorem copied_entry (f : ℤ → Fin (a+4)) (p : ℤ) (n i : ℕ) (hi : i < 2*n) :
    (copied f p n)[i]'(by simpa using hi) = readBit (f (p-i)) := by
  induction n generalizing p i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [copied]
    | succ i =>
      cases i with
      | zero => simp [copied]
      | succ i =>
        have hi' : i < 2*n := by omega
        change (copied f (p-2) n)[i]'(by simpa using hi') = _
        rw [ih (p-2) i hi']
        congr 2
        push_cast
        ring

/-- Reading beyond a finite accumulator on a blank background gives a false
bit, including every cell of the padding region. -/
theorem accumulator_cell (acc : List Bool) (pa : ℤ) (i : ℕ) :
    readBit (putWord (fun _ => (blank : Fin (a+4))) pa (acc.map bitSymbol) (pa+i)) =
      acc.getD i false := by
  by_cases hi : i < acc.length
  · rw [WordSegments.get _ _ _ i (by simpa using hi),List.getElem_map,
      DoubleClockReverseCopy.readBit_symbol,List.getD_eq_getElem _ _ hi]
  · rw [putWord_outside _ _ _ _ (Or.inr (by simp only [List.length_map]; omega)),
      DoubleClockReverseCopy.readBit_blank,List.getD_eq_default _ _ (by omega)]

def padded (acc : List Bool) (n : ℕ) := (acc ++ List.replicate (2*n-acc.length) false).reverse

@[simp] theorem padded_length (acc : List Bool) (n : ℕ) (hlen : acc.length ≤ 2*n) :
    (padded acc n).length = 2*n := by
  simp only [padded,List.length_reverse,List.length_append,List.length_replicate]
  omega

/-- This is an equality of literal bit lists, not only an equality of values. -/
theorem copied_accumulator (acc : List Bool) (pa : ℤ) (n : ℕ) (hlen : acc.length ≤ 2*n) :
    copied (putWord (fun _ => (blank : Fin (a+4))) pa (acc.map bitSymbol)) (pa+2*n-1) n =
      padded acc n := by
  apply List.ext_getElem
  · rw [DoubleClockReverseCopy.copied_length,padded_length acc n hlen]
  · intro i hi hj
    have hi' : i < 2*n := by simpa only [DoubleClockReverseCopy.copied_length] using hi
    rw [copied_entry _ _ n i hi']
    have he : pa+2*(n : ℤ)-1-i = pa+((2*n-1-i : ℕ) : ℤ) := by omega
    rw [he,accumulator_cell]
    unfold padded at hj
    change acc.getD (2*n-1-i) false = (acc ++ List.replicate (2*n-acc.length) false).reverse[i]
    rw [List.getElem_reverse]
    have hl : (acc ++ List.replicate (2*n-acc.length) false).length = 2*n := by
      simp only [List.length_append,List.length_replicate]
      omega
    simp only [hl]
    by_cases hk : 2*n-1-i < acc.length
    · rw [List.getElem_append_left hk,List.getD_eq_getElem _ _ hk]
    · rw [List.getElem_append_right (by omega),List.getElem_replicate,
        List.getD_eq_default _ _ (by omega)]

/-- High zero padding in little-endian order does not change the represented
integer after conversion to the required most-significant-first convention. -/
theorem padded_value (acc : List Bool) (n : ℕ) : binaryValue (padded acc n) = Counter.value acc := by
  rw [← ElementaryMultiplyCore.value_reverse]
  simp only [padded,List.reverse_reverse]
  exact Registers.value_padding acc _

theorem copied_accumulator_value (acc : List Bool) (pa : ℤ) (n : ℕ) (hlen : acc.length ≤ 2*n) :
    binaryValue (copied (putWord (fun _ => (blank : Fin (a+4))) pa (acc.map bitSymbol))
      (pa+2*n-1) n) = Counter.value acc := by
  rw [copied_accumulator acc pa n hlen,padded_value]

/-- The accumulator begins at -n, so the first output read is at n-1. -/
theorem horner_output {n : ℕ} {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    copied (putWord (fun _ => (blank : Fin (a+4))) (-(n : ℤ))
      ((BinaryMultiply.horner x.reverse y.reverse).map bitSymbol)) (n-1) n =
      padded (BinaryMultiply.horner x.reverse y.reverse) n := by
  have hl := BinaryMultiply.horner_length x.reverse y.reverse
  simp only [List.length_reverse,hx,hy] at hl
  have hh := copied_accumulator (a := a) (BinaryMultiply.horner x.reverse y.reverse) (-(n : ℤ)) n (by omega)
  have hp : -(n : ℤ)+2*n-1 = n-1 := by ring
  rw [hp] at hh
  exact hh

theorem horner_output_length {n : ℕ} {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    (copied (putWord (fun _ => (blank : Fin (a+4))) (-(n : ℤ))
      ((BinaryMultiply.horner x.reverse y.reverse).map bitSymbol)) (n-1) n).length = 2*n := by
  rw [horner_output hx hy]
  apply padded_length
  have hl := BinaryMultiply.horner_length x.reverse y.reverse
  simp only [List.length_reverse,hx,hy] at hl
  omega

theorem horner_output_value {n : ℕ} {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    binaryValue (copied (putWord (fun _ => (blank : Fin (a+4))) (-(n : ℤ))
      ((BinaryMultiply.horner x.reverse y.reverse).map bitSymbol)) (n-1) n) =
      binaryValue x*binaryValue y := by
  rw [horner_output hx hy,padded_value,ElementaryMultiplyCore.accumulator_value]

end IntegerMultBounds.Machine.ElementaryMultiplyOutputData
