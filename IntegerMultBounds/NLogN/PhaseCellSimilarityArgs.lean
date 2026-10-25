module

public import IntegerMultBounds.NLogN.PhaseCellCoefficientArgs

/-! Natural unreduced similarity arguments, with the original upward-tie
nearest rounding. The residue construction avoids signed arithmetic and gcds. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRationalArgs

/-- Residue of the shifted coordinate used by upward-tie nearest rounding. -/
def similarityResidue (s t j : ℕ) : ℕ := (2 * t * j + s) % (2 * s)

/-- Natural numerator for the similarity potential. -/
def similarityNumerator (s t u j : ℕ) : ℕ :=
  u * similarityResidue s t j * (2 * s - similarityResidue s t j)

/-- Positive denominator when the sampling ratio is strictly greater than one. -/
def similarityDenominator (s t : ℕ) : ℕ := 4 * s * (t - s)

theorem similarityDenominator_pos {s t : ℕ} (hs : 0 < s) (hst : s < t) :
    0 < similarityDenominator s t := by
  unfold similarityDenominator
  exact Nat.mul_pos (Nat.mul_pos (by decide) hs) (Nat.sub_pos_of_lt hst)

/-- The modular construction computes the exact potential, including ties. -/
theorem similarity_ratio (s t u j : ℕ) (hs : 0 < s) (hst : s < t) :
    (similarityNumerator s t u j : ℚ) / similarityDenominator s t =
      potentialQ s t u j := by
  have hr : similarityResidue s t j < 2 * s := Nat.mod_lt _ (by omega)
  have hdiv := Nat.mod_add_div (2 * t * j + s) (2 * s)
  have hdivQ : (similarityResidue s t j : ℚ) +
      2 * s * (( (2 * t * j + s) / (2 * s) : ℕ) : ℚ) = 2 * t * j + s := by
    exact_mod_cast hdiv
  have hnear : nearestQ s t (j : ℤ) = ((2 * t * j + s) / (2 * s) : ℕ) := by
    unfold nearestQ
    norm_cast
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hts : (t : ℚ) - s ≠ 0 := by
    have : (s : ℚ) < t := by exact_mod_cast hst
    linarith
  simp only [similarityNumerator, similarityDenominator, Nat.cast_mul,
    Nat.cast_sub (Nat.le_of_lt hr), Nat.cast_sub (Nat.le_of_lt hst),
    Nat.cast_ofNat, potentialQ, betaQ, hnear, Int.cast_natCast]
  have hz : (t : ℚ) * j - s * (((2 * t * j + s) / (2 * s) : ℕ) : ℚ) =
      ((similarityResidue s t j : ℚ) - s) / 2 := by nlinarith [hdivQ]
  field_simp
  rw [hz]
  ring

/-- The argument workspace depends on the modulus, not the ambient index. -/
theorem similarityNumerator_le (s t u j : ℕ) :
    similarityNumerator s t u j ≤ u * s ^ 2 := by
  by_cases hs : s = 0
  · subst s
    simp [similarityNumerator, similarityResidue]
  have hr : similarityResidue s t j < 2 * s := Nat.mod_lt _ (by omega)
  have he : similarityResidue s t j + (2 * s - similarityResidue s t j) = 2 * s := by omega
  have hb : similarityResidue s t j * (2 * s - similarityResidue s t j) ≤ s ^ 2 := by
    nlinarith [sq_nonneg ((similarityResidue s t j : ℤ) - s)]
  exact (Nat.mul_assoc _ _ _).le.trans (Nat.mul_le_mul_left u hb)

/-- Unreduced natural arguments feed the same corrected exponential evaluator. -/
theorem similarityArg_ratio (s t u j : ℕ) (hs : 0 < s) (hst : s < t) :
    (similarityNumerator s t u j : ℚ) / similarityDenominator s t =
      ((PhaseCellConcreteCoefficients.similarityArg s t u j).aa : ℚ) /
        (PhaseCellConcreteCoefficients.similarityArg s t u j).b := by
  have hpos : 0 ≤ potentialQ s t u j := by
    rw [← similarity_ratio s t u j hs hst]
    positivity
  rw [similarity_ratio s t u j hs hst]
  exact (natural_encoding _ hpos).symm

/-- Exact sample identity: the correction by two is retained. -/
theorem similarity_sample (P s t u j : ℕ) (hs : 0 < s) (hst : s < t) :
    PhaseCellConcreteCoefficients.similarity P s t u j =
      PhaseCellExpSample.sample P (similarityNumerator s t u j)
        (similarityDenominator s t) := by
  unfold PhaseCellConcreteCoefficients.similarity
    PhaseCellExecutableCoefficients.ExpArg.value PhaseCellExpSample.sample
  rw [PhaseCellIntegerGenerators.correctedNumerator_ratio P _ _ _ _
    (similarityArg_ratio s t u j hs hst)]

end IntegerMultBounds.NLogN.PhaseCellRationalArgs
