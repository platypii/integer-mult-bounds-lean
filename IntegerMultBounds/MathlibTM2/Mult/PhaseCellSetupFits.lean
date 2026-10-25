module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerWords
public import IntegerMultBounds.NLogN.PhaseCellIntegerBounds

/-! # Signed setup words for all integer generator row operations

The width covers stored vectors, row products, arbitrary partial accumulators
and the reciprocal numerator. This is a width contract, not a setup execution
or peak-space theorem.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

private theorem fits_of_integer_power {W e : ℕ} (hW : e + 2 ≤ W) (z : ℤ)
    (hz : |z| ≤ (2 : ℤ) ^ e) : Fits W (⟨z, 0⟩ : GaussianInt) := by
  constructor
  · exact hz.trans_lt (pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 2) (by omega))
  · change |(0 : ℤ)| < (2 : ℤ) ^ (W - 1)
    simpa only [abs_zero] using pow_pos (by norm_num : (0 : ℤ) < 2) (W - 1)

theorem coefficientNumerator_fits {P W : ℕ} (hW : P + 2 ≤ W) (hP : 13 ≤ P)
    (s t u band k : ℕ) :
    Fits W (⟨coefficientNumerator P s t u band k, 0⟩ : GaussianInt) :=
  fits_of_integer_power hW _ (coefficientNumerator_abs_le hP s t u band k)

theorem rowProduct_fits {P s t u band L n W : ℕ} (hW : P * (n + 1) + 3 ≤ W)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (i : ℕ) (z : ℤ) (hz : z ∈ rowTerms P s t u band L n i) :
    Fits W (⟨z, 0⟩ : GaussianInt) :=
  fits_of_integer_power (e := P * (n + 1) + 1) (by omega) z (rowTerms_abs_le hP hs hst hu hn i z hz)

theorem rowPartial_fits {P s t u band L n l W : ℕ} (hW : P * (n + 1) + l + 3 ≤ W)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n) (hL : L ≤ 2 ^ l)
    (i : ℕ) (xs : List ℤ) (hxs : xs.Sublist (rowTerms P s t u band L n i)) :
    Fits W (⟨xs.sum, 0⟩ : GaussianInt) :=
  fits_of_integer_power (e := P * (n + 1) + l + 1) (by omega) xs.sum (rowPartial_abs_le hP hs hst hu hn hL i xs hxs)

theorem rowAccumulator_fits {P s t u band L n l W : ℕ} (hW : P * (n + 1) + l + 4 ≤ W)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n) (hL : L ≤ 2 ^ l)
    (i : ℕ) (xs : List ℤ) (hxs : xs.Sublist (rowTerms P s t u band L n i)) :
    Fits W (⟨(2 : ℤ) ^ (P * (n + 1)) * (if i = 0 then 1 else 0) - xs.sum, 0⟩ : GaussianInt) :=
  fits_of_integer_power (e := P * (n + 1) + l + 2) (by omega) _ (rowAccumulator_abs_le hP hs hst hu hn hL i xs hxs)

/-- One conservative setup width includes the reciprocal numerator and one
extra iteration's arithmetic workspace. -/
def integerSetupWidth (P q n l : ℕ) : ℕ := P * (n + 1) + q + l + 5

theorem integerSetupWidth_bounds (P q n l : ℕ) :
    P * n + 3 ≤ integerSetupWidth P q n l ∧
    q + P * n + 2 ≤ integerSetupWidth P q n l ∧
    P * (n + 1) + l + 4 ≤ integerSetupWidth P q n l := by
  unfold integerSetupWidth
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · omega

theorem integerSetupWidth_mono {n m : ℕ} (P q l : ℕ) (hn : n ≤ m) :
    integerSetupWidth P q n l ≤ integerSetupWidth P q m l := by
  have hm := Nat.mul_le_mul_left P (Nat.add_le_add_right hn 1)
  unfold integerSetupWidth
  omega

/-- The setup word has enough high sign bits to copy the complete runtime word
after dropping the dyadic scale. No sign extension is needed by the machine. -/
theorem integerSetupWidth_slice {P q n l : ℕ} (hP : 4 ≤ P) (hqr : q ≤ P * n + 1) :
    P * n + 1 - q + (2 * q + 8) ≤ integerSetupWidth P q n l := by
  have hsum := Nat.sub_add_cancel hqr
  unfold integerSetupWidth
  nlinarith only [hsum, hP]

theorem integerSetupWidth_scale (P q n l : ℕ) :
    P * n + 1 ≤ integerSetupWidth P q n l := by
  unfold integerSetupWidth
  nlinarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
