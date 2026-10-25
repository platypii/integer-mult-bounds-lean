module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversedColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergeRange

/-! # Signed decoding and accuracy of the emitted second generator -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.ToeplitzInverse

theorem reversedColumn_decode {A P s t u band L q n : ℕ} (hA : 4 ≤ A) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hq : 2 ≤ q) (hn : 1 ≤ n)
    (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hsrc : S.R 113 = cstream A (2 * q + 8) (reversedColumnWords P s t u band L q n) ++ tail)
    (i : ℕ) (hi : i < L) :
    decodeWord (((S.R 113).drop (i * (2 * q + 8))).take (2 * q + 8)) =
      block (reversedColumnWords P s t u band L q n) i := by
  have hi' : i < (reversedColumnWords P s t u band L q n).length := by simpa using hi
  rw [hsrc, cstream_word _ _ tail i hi', decodeWord_of_fits hA (by omega) _
    (fits_of_disk (q := q) (by omega) _
      (reversedColumnWords_disk hP hs hst hu hq hn _ (List.getElem_mem hi')))]
  simp only [block, List.getElem?_eq_getElem hi', Option.getD_some]

theorem reversedColumn_error_precision {A P s t u band L q j : ℕ} (hA : 4 ≤ A) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hq : j + 2 ≤ q)
    (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hsrc : S.R 113 = cstream A (2 * q + 8) (reversedColumnWords P s t u band L q (j + 2)) ++ tail)
    (i : ℕ) (hi : i < L) :
    |2 * (value q (decodeWord (((S.R 113).drop (i * (2 * q + 8))).take (2 * q + 8)))).re -
      rev L (natInv L (PhaseCellToeplitz.coeff P s t u band)) i| ≤ 1 / (2 : ℝ) ^ j := by
  rw [reversedColumn_decode hA hP hs hst hu (by omega) (by omega) S tail hsrc i hi]
  exact reversedColumnWords_error_precision hP hs hst hu hq i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
