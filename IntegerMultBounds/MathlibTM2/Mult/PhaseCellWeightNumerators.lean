module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightData
public import IntegerMultBounds.NLogN.PhaseCellSimilarityArgs

/-! Exact natural divisions for the runtime similarity and reciprocal words.
These formulas use the corrected executable sample, rather than an ideal floor
of the real exponential. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN

/-- Natural division is exactly the rational word encoder on a natural ratio. -/
theorem rationalWord_nat_ratio (q a b : ℕ) :
    rationalWord q ((a : ℚ) / b) = ⟨((2 ^ q * a / b : ℕ) : ℤ), 0⟩ := by
  unfold rationalWord
  congr 1
  rw [← mul_div_assoc]
  norm_cast

/-- Actual similarity numerator at an ambient coordinate. -/
def similarityGridNumerator (P s t u j : ℕ) : ℕ :=
  PhaseCellExpSample.numerator P
    (PhaseCellRationalArgs.similarityNumerator s t u j)
    (PhaseCellRationalArgs.similarityDenominator s t)

theorem similarity_grid (P s t u j : ℕ) (hs : 0 < s) (hst : s < t) :
    PhaseCellConcreteCoefficients.similarity P s t u j =
      (similarityGridNumerator P s t u j : ℚ) / (2 : ℚ) ^ P := by
  exact PhaseCellRationalArgs.similarity_sample P s t u j hs hst

/-- Two sample guard bits suffice before multiplication by the output scale. -/
theorem similarityGridNumerator_fits {q P s t u j V : ℕ}
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hV : q + P + 2 ≤ V) :
    2 ^ q * similarityGridNumerator P s t u j < 2 ^ V := by
  have hraw := PhaseCellIntegerGenerators.expPiNat_neg_lt_pow hP
    (le_refl (P + 2)) (PhaseCellRationalArgs.similarityNumerator s t u j)
    (PhaseCellRationalArgs.similarityDenominator s t)
    (PhaseCellRationalArgs.similarityDenominator_pos hs hst)
  have hn : similarityGridNumerator P s t u j < 2 ^ (P + 2) :=
    (Nat.sub_le _ 2).trans_lt hraw
  have hmul := Nat.mul_lt_mul_of_pos_left hn (by positivity : 0 < 2 ^ q)
  rw [← pow_add] at hmul
  exact hmul.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

/-- Final similarity weights require only unsigned division. -/
theorem similarity_output_word (q P s t u j : ℕ) (hs : 0 < s) (hst : s < t) :
    rationalWord q (PhaseCellConcreteCoefficients.similarity P s t u j) =
      ⟨((2 ^ q * similarityGridNumerator P s t u j / 2 ^ P : ℕ) : ℤ), 0⟩ := by
  rw [similarity_grid P s t u j hs hst]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    rationalWord_nat_ratio q (similarityGridNumerator P s t u j) (2 ^ P)

/-- Reciprocal weights use the same sampled numerator, with no new rounding. -/
theorem similarity_reciprocal_word (q P s t u j : ℕ) (hs : 0 < s) (hst : s < t) :
    reciprocalWeightWord q (PhaseCellConcreteCoefficients.similarity P s t u j) =
      ⟨((2 ^ (q + P) / similarityGridNumerator P s t u j : ℕ) : ℤ), 0⟩ := by
  unfold reciprocalWeightWord
  rw [similarity_grid P s t u j hs hst, one_div_div]
  have he := rationalWord_nat_ratio q (2 ^ P) (similarityGridNumerator P s t u j)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_add] using he

/-- The machine reads the original ambient coordinate, including wraparound. -/
theorem weightData_grid (s t p u : ℕ) (lo : ZMod s) (k : ℕ)
    (hs : 0 < s) (hst : s < t) :
    weightData s t p u lo k =
      (similarityGridNumerator (2 ^ 15 * p) s t u (lo + (k : ZMod s)).val : ℚ) /
        (2 : ℚ) ^ (2 ^ 15 * p) := by
  exact similarity_grid _ _ _ _ _ hs hst

/-- Exact output-stage word at the original ambient cell coordinate. -/
theorem weightData_output_word (q s t p u : ℕ) (lo : ZMod s) (k : ℕ)
    (hs : 0 < s) (hst : s < t) :
    rationalWord q (weightData s t p u lo k) =
      ⟨((2 ^ q * similarityGridNumerator (2 ^ 15 * p) s t u
        (lo + (k : ZMod s)).val / 2 ^ (2 ^ 15 * p) : ℕ) : ℤ), 0⟩ := by
  exact similarity_output_word _ _ _ _ _ _ hs hst

/-- Exact input-stage reciprocal word at the same ambient cell coordinate. -/
theorem weightData_reciprocal_word (q s t p u : ℕ) (lo : ZMod s) (k : ℕ)
    (hs : 0 < s) (hst : s < t) :
    reciprocalWeightWord q (weightData s t p u lo k) =
      ⟨((2 ^ (q + 2 ^ 15 * p) / similarityGridNumerator (2 ^ 15 * p) s t u
        (lo + (k : ZMod s)).val : ℕ) : ℤ), 0⟩ := by
  exact similarity_reciprocal_word _ _ _ _ _ _ hs hst

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
