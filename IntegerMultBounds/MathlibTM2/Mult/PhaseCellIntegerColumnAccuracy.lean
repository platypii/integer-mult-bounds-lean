module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerColumn

/-! # Numerical accuracy of the actual signed integer column words

The retained context is returned by the executed generator. Signed decoding
recovers its integer entries; division by their known dyadic scale gives the
existing rational generator error and a positive reciprocal divisor.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellIntegerGenerators IntegerMultBounds.NLogN.ToeplitzInverse

theorem IntegerGeneratorContext.column_error {A P s t u band L M w : ℕ}
    {tailX tailF : List (Fin (A + 4))} {S : Stacks 117 A}
    (h : IntegerGeneratorContext P s t u band L (M + 1) w tailX tailF S)
    (hA : 4 ≤ A) (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (i : ℕ) (hi : i < L) :
    |((decodeWord (((S.R 110).drop (i * w)).take w)).re : ℝ) / (2 : ℝ) ^ (P * (M + 1)) -
      col (natInv L (PhaseCellToeplitz.coeff P s t u band)) i| ≤ 1 / (2 : ℝ) ^ M := by
  rw [h.row.decode hA i hi, rowColumnWords_getD P s t u band L (M + 1) i hi]
  have hratio :
      (((columnNumerators P s t u band L (M + 1)).getD i 0 : ℤ) : ℝ) / (2 : ℝ) ^ (P * (M + 1)) =
        ((PhaseCellGeneratorData.column P s t u band L (M + 1)).getD i 0 : ℝ) := by
    exact_mod_cast columnNumerators_getD P s t u band L (M + 1) i
  simpa only [hratio] using PhaseCellGeneratorData.column_error_precision hP hs hst hu M i hi

theorem IntegerGeneratorContext.corner_pos {A P s t u band L M w : ℕ}
    {tailX tailF : List (Fin (A + 4))} {S : Stacks 117 A}
    (h : IntegerGeneratorContext P s t u band L (M + 1) w tailX tailF S)
    (hA : 4 ≤ A) (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L) :
    0 < (decodeWord ((S.R 110).take w)).re := by
  have hd := h.row.decode hA 0 hL
  simp only [Nat.zero_mul, List.drop_zero, rowColumnWords_getD P s t u band L (M + 1) 0 hL] at hd
  rw [hd]
  exact columnNumerators_corner_pos hP hs hst hu hL (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
