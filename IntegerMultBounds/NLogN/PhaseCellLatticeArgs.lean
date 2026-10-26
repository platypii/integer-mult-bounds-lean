module

public import IntegerMultBounds.NLogN.PhaseCellSimilarityArgs
public import IntegerMultBounds.NLogN.PhaseCellCrossCell

/-! Natural unreduced arguments for direct cross-cell coefficients. Upward-tie
nearest rounding is retained; natural subtraction is justified before use. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRationalArgs

/-- Absolute difference, expressed using natural arithmetic only. -/
def naturalDistance (a b : ℕ) : ℕ := (a-b)+(b-a)

def nearestNatural (s t j : ℕ) : ℕ := (2*t*j+s)/(2*s)

def latticeDistance (s t j k : ℕ) : ℕ :=
  naturalDistance (t*k) (s*nearestNatural s t j)

def latticeNumerator (s t u j k : ℕ) : ℕ :=
  u*(latticeDistance s t j k^2-latticeDistance s t k k^2)

theorem naturalDistance_sq (a b : ℕ) :
    (naturalDistance a b : ℚ)^2 = ((a : ℚ)-b)^2 := by
  by_cases hab : a ≤ b
  · simp only [naturalDistance,Nat.sub_eq_zero_of_le hab,zero_add,Nat.cast_sub hab]
    ring
  · have hba : b ≤ a := by omega
    simp only [naturalDistance,Nat.sub_eq_zero_of_le hba,add_zero,Nat.cast_sub hba]

theorem nearestNatural_cast (s t j : ℕ) :
    nearestQ s t (j : ℤ) = (nearestNatural s t j : ℕ) := by
  unfold nearestQ nearestNatural
  norm_cast

/-- The difference of integer squares is the original lattice exponent. -/
theorem latticeDistance_ratio (s t j k : ℕ) (hs : 0 < s) :
    ((latticeDistance s t j k : ℚ)^2-(latticeDistance s t k k : ℚ)^2)/(s : ℚ)^2 =
      PhaseCellCrossCell.latticeQ s t 1 j ((k : ℤ)-j) := by
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [latticeDistance,naturalDistance_sq,Nat.cast_mul,
    PhaseCellCrossCell.latticeQ,betaQ,nearestNatural_cast,Nat.cast_one,one_mul,
    Int.cast_sub,Int.cast_natCast,add_sub_cancel]
  field_simp
  ring

/-- Nearest rounding at the destination makes the subtracted square smaller. -/
theorem latticeDistance_sq_le (s t j k : ℕ) (hs : 0 < s) (hst : s < t) :
    latticeDistance s t k k^2 ≤ latticeDistance s t j k^2 := by
  have hh := PhaseCellCrossCell.latticeQ_nonneg s t 1 hs hst (j : ℤ) ((k : ℤ)-j)
  rw [← latticeDistance_ratio s t j k hs] at hh
  have hp : (0 : ℚ) < (s : ℚ)^2 := by positivity
  have hn := (le_div_iff₀ hp).mp hh
  have hle : (latticeDistance s t k k : ℚ)^2 ≤ (latticeDistance s t j k : ℚ)^2 := by linarith
  exact_mod_cast hle

theorem latticeNumerator_ratio (s t u j k : ℕ) (hs : 0 < s) (hst : s < t) :
    (latticeNumerator s t u j k : ℚ)/(s : ℚ)^2 =
      PhaseCellCrossCell.latticeQ s t u j ((k : ℤ)-j) := by
  have he := latticeDistance_ratio s t j k hs
  simp only [latticeNumerator,Nat.cast_mul,Nat.cast_sub (latticeDistance_sq_le s t j k hs hst),
    Nat.cast_pow]
  rw [mul_div_assoc,he]
  simp [PhaseCellCrossCell.latticeQ]

/-- The machine's unreduced argument gives exactly the selected corrected sample. -/
theorem direct_sample (P s t u j k : ℕ) (hs : 0 < s) (hst : s < t) :
    PhaseCellCrossCell.direct P s t u j k =
      PhaseCellExpSample.sample P (latticeNumerator s t u j k) (s^2) := by
  have harg : (latticeNumerator s t u j k : ℚ)/(s^2 : ℕ) =
      ((PhaseCellConcreteCoefficients.encode
        (PhaseCellCrossCell.latticeQ s t u j ((k : ℤ)-j))).aa : ℚ)/
      (PhaseCellConcreteCoefficients.encode
        (PhaseCellCrossCell.latticeQ s t u j ((k : ℤ)-j))).b := by
    dsimp only [PhaseCellConcreteCoefficients.encode]
    rw [PhaseCellRationalArgs.natural_encoding _
      (PhaseCellCrossCell.latticeQ_nonneg s t u hs hst _ _)]
    simpa only [Nat.cast_pow] using latticeNumerator_ratio s t u j k hs hst
  unfold PhaseCellCrossCell.direct PhaseCellExecutableCoefficients.ExpArg.value PhaseCellExpSample.sample
  rw [PhaseCellIntegerGenerators.correctedNumerator_ratio P _ _ _ _ harg.symm]

end IntegerMultBounds.NLogN.PhaseCellRationalArgs
