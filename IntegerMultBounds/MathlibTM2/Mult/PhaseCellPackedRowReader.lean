module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! A packed row reader inside its owned interval ignores any borrowed suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem packedIntervalRead_append_row {A s : ℕ} (q w a : ℕ)
    (row : List GaussianInt) (tail : List (Fin (A+4))) (i : ZMod s)
    (ha : a ≤ i.val) (hi : i.val < a+row.length) :
    packedIntervalRead q w a (cstream A w row++tail) i = packedIntervalRead q w a (cstream A w row) i := by
  have hj : i.val-a < row.length := by omega
  have he := cstream_word (A := A) w row tail (i.val-a) hj
  have he₀ := cstream_word (A := A) w row [] (i.val-a) hj
  simp only [List.append_nil] at he₀
  simp only [packedIntervalRead,he,he₀]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
