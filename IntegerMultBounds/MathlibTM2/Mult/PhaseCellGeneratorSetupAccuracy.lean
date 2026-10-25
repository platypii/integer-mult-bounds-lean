module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratorSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputBounds

/-! # Accuracy of all three runtime banks produced by generator setup -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.ToeplitzInverse

theorem generatorBank_reciprocal {A P s t u band L q W n : ℕ}
    (hA : 4 ≤ A) (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (hL : 0 < L) (hn : 1 ≤ n) (S : Stacks 117 A) :
    decodeWord ((generatorBank S P s t u band L q W n).R 96) =
      reciprocalWord P s t u band L q n := by
  have hfit : Fits (2 * q + 8) (reciprocalWord P s t u band L q n) := by
    apply fits_of_norm_value_bound _ 2 (reciprocalWord_norm hP hs hst hu hL hn)
    rw [← pow_succ]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  simpa only [generatorBank, Function.update_self] using decodeWord_of_fits hA (by omega) _ hfit

/-- At the shared precision choice the generated first column, shifted reverse
and reciprocal all meet the kernel's stage tolerance after actual signed decoding. -/
theorem generatorBank_accuracy {A P s t u band L q W j : ℕ}
    (hA : 4 ≤ A) (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (hL : 0 < L) (hq : j + 2 ≤ q) (S : Stacks 117 A) :
    let S' := generatorBank S P s t u band L q W (j + 2)
    (∀ i < L,
      |2 * (value q (decodeWord (((S'.R 111).drop (i * (2 * q + 8))).take (2 * q + 8)))).re -
        col (natInv L (PhaseCellToeplitz.coeff P s t u band)) i| ≤ 1 / (2 : ℝ) ^ j) ∧
    (∀ i < L,
      |2 * (value q (decodeWord (((S'.R 113).drop (i * (2 * q + 8))).take (2 * q + 8)))).re -
        rev L (natInv L (PhaseCellToeplitz.coeff P s t u band)) i| ≤ 1 / (2 : ℝ) ^ j) ∧
    |(value q (decodeWord (S'.R 96))).re -
      1 / natInv L (PhaseCellToeplitz.coeff P s t u band) 0 0| ≤ 1 / (2 : ℝ) ^ j := by
  let S' := generatorBank S P s t u band L q W (j + 2)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    apply encodedColumn_error_precision hA hP hs hst hu hq S' (S.R 111) _ i hi
    simp [S', generatorBank, encodedColumnBank, generatedColumn, counterR, cr, OutputPlacement.code]
  · intro i hi
    apply reversedColumn_error_precision hA hP hs hst hu hq S' (S.R 113) _ i hi
    simp [S', generatorBank, encodedColumnBank, generatedColumn, counterR, cr, OutputPlacement.code]
  · rw [generatorBank_reciprocal hA hP hs hst hu hL (by omega) S]
    exact reciprocalWord_error_precision hP hs hst hu hq hL

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
