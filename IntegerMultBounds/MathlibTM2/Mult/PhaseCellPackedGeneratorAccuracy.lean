module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratorPage

/-! # Numerical accuracy at the packed runtime page's physical word offsets -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.ToeplitzInverse

/-- Packing preserves the proved numerical endpoint at offsets i, L+i and 2L. -/
theorem packedGeneratorBank_accuracy {A P s t u band L q W j : ℕ}
    (hA : 4 ≤ A) (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (hL : 0 < L) (hq : j + 2 ≤ q) (S : Stacks 117 A) :
    let S' := packedGeneratorBank S P s t u band L q W (j + 2)
    (∀ i < L,
      |2 * (value q (decodeWord (((S'.R 110).drop (i * (2 * q + 8))).take (2 * q + 8)))).re -
        col (natInv L (PhaseCellToeplitz.coeff P s t u band)) i| ≤ 1 / (2 : ℝ) ^ j) ∧
    (∀ i < L,
      |2 * (value q (decodeWord (((S'.R 110).drop ((L + i) * (2 * q + 8))).take (2 * q + 8)))).re -
        rev L (natInv L (PhaseCellToeplitz.coeff P s t u band)) i| ≤ 1 / (2 : ℝ) ^ j) ∧
    |(value q (decodeWord (((S'.R 110).drop (2 * L * (2 * q + 8))).take (2 * q + 8)))).re -
      1 / natInv L (PhaseCellToeplitz.coeff P s t u band) 0 0| ≤ 1 / (2 : ℝ) ^ j := by
  let S' := packedGeneratorBank S P s t u band L q W (j + 2)
  have hpage : S'.R 110 = generatorPage A P s t u band L q (j + 2) ++ S.R 110 := by
    simp [S', packedGeneratorBank]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have h := encodedColumn_error_precision (band := band) hA hP hs hst hu hq
      { S' with R := Function.update S'.R 111 (S'.R 110) }
      (cstream A (2 * q + 8) (reversedColumnWords P s t u band L q (j + 2)) ++
        (csyms A (2 * q + 8) (reciprocalWord P s t u band L q (j + 2)) ++ S.R 110))
      (by simp [hpage, generatorPage, List.append_assoc]) i hi
    simpa only [Function.update_self] using h
  · intro i hi
    have hdrop : (S'.R 110).drop (L * (2 * q + 8)) =
        cstream A (2 * q + 8) (reversedColumnWords P s t u band L q (j + 2)) ++
          (csyms A (2 * q + 8) (reciprocalWord P s t u band L q (j + 2)) ++ S.R 110) := by
      rw [hpage, show L * (2 * q + 8) =
        (cstream A (2 * q + 8) (columnWords P s t u band L q (j + 2))).length by simp]
      simp only [generatorPage, List.append_assoc, List.drop_left]
    have h := reversedColumn_error_precision (band := band) hA hP hs hst hu hq
      { S' with R := Function.update S'.R 113 ((S'.R 110).drop (L * (2 * q + 8))) }
      (csyms A (2 * q + 8) (reciprocalWord P s t u band L q (j + 2)) ++ S.R 110)
      (by simpa only [Function.update_self] using hdrop) i hi
    simpa only [Function.update_self, List.drop_drop, ← Nat.add_mul] using h
  · have hscalar := (generatorPage_reads A P s t u band L q (j + 2) (S.R 110)).2.2
    rw [← hpage] at hscalar
    rw [hscalar]
    have hd := generatorBank_reciprocal (band := band) (q := q) (W := W) hA hP hs hst hu hL (by omega : 1 ≤ j + 2) S
    change decodeWord (csyms A (2 * q + 8) (reciprocalWord P s t u band L q (j + 2))) = _ at hd
    rw [hd]
    exact reciprocalWord_error_precision hP hs hst hu hq hL

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
