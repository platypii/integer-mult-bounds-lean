module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedGenerators

/-! # The second runtime generator is a shifted reversal of the first -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN

/-- Encoding commutes with the shifted reverse, including the zero head. -/
theorem reversedColumnWords_eq {P s t u band L q n : ℕ} (hL : 0 < L) :
    reversedColumnWords P s t u band L q n =
      0 :: ((columnWords P s t u band L q n).drop 1).reverse := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    have hiL : i < L := by simpa using hi
    cases i with
    | zero =>
      simp [reversedColumnWords, normalizedWords, PhaseCellGeneratorData.reversedColumn]
    | succ i =>
      have he : 1 + (L - 1 - 1 - i) = L - (i + 1) := by omega
      simp only [reversedColumnWords, normalizedWords, List.getElem_map,
        PhaseCellGeneratorData.reversedColumn, List.getElem_range, Nat.add_one_ne_zero,
        ↓reduceIte, List.getElem_cons_succ, List.getElem_reverse, List.getElem_drop,
        columnWords, List.length_map, PhaseCellGeneratorData.column_length,
        List.length_drop, he]
      rw [List.getD_eq_getElem _ _ (by simpa using (show L - (i + 1) < L by omega))]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
