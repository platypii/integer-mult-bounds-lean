module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightNumerators
public import IntegerMultBounds.NLogN.PhaseCellCoefficientArgs
public import IntegerMultBounds.NLogN.PhaseCellLatticeArgs

/-! The within-cell entry is encoded by one natural division of the actual
corrected sample numerators. No intermediate q-grid rounding is introduced. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

def distanceGridNumerator (P s t u d : ℕ) : ℕ := PhaseCellExpSample.numerator P (u*t*d^2) s

theorem gaussian_sample_grid (P s t u : ℕ) (δ : ℤ) :
    (PhaseCellConcreteCoefficients.gaussianArg s t u δ).value P =
      (distanceGridNumerator P s t u δ.natAbs : ℚ)/(2 : ℚ)^P := by
  have he := gaussianArg_ratio s t u δ.natAbs
  have hδ : PhaseCellConcreteCoefficients.gaussianArg s t u δ =
      PhaseCellConcreteCoefficients.gaussianArg s t u (δ.natAbs : ℕ) := by
    unfold PhaseCellConcreteCoefficients.gaussianArg PhaseCellRationalArgs.gaussianQ
    congr 2
    have hh : ((δ.natAbs : ℕ) : ℚ)^2 = (δ : ℚ)^2 := by
      norm_cast
      simp [Int.natCast_natAbs, sq_abs]
    simpa only [Int.cast_natCast] using hh.symm
  rw [hδ]
  unfold PhaseCellExecutableCoefficients.ExpArg.value PhaseCellExpSample.sample distanceGridNumerator
  rw [correctedNumerator_ratio P _ _ _ _ he.symm]

/-- Zero denominators retain the rational and natural division convention. -/
theorem within_coefficient_word (q P s t u band j k : ℕ) (hs : 0 < s) (hst : s < t)
    (hjk : j ≠ k) (hband : ((k : ℤ)-(j : ℤ)).natAbs ≤ band) :
    rationalWord q (PhaseCellConcreteCoefficients.entry P s t u band j k) =
      (⟨((2^q*(similarityGridNumerator P s t u j*
        distanceGridNumerator P s t u ((k : ℤ)-(j : ℤ)).natAbs)/
        (similarityGridNumerator P s t u k*2^P) : ℕ) : ℤ),0⟩ : GaussianInt) := by
  have he : PhaseCellConcreteCoefficients.entry P s t u band j k =
      ((similarityGridNumerator P s t u j*distanceGridNumerator P s t u
        ((k : ℤ)-(j : ℤ)).natAbs : ℕ) : ℚ)/
        ((similarityGridNumerator P s t u k*2^P : ℕ) : ℚ) := by
    simp only [PhaseCellConcreteCoefficients.entry,PhaseCellExecutableCoefficients.entry]
    rw [if_neg (by exact_mod_cast hjk)]
    have hδ : (k : ℤ)-(j : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm hjk)
    simp only [PhaseCellExecutableCoefficients.kernel,if_neg hδ,if_pos hband]
    rw [gaussian_sample_grid,← PhaseCellConcreteCoefficients.similarity,
      ← PhaseCellConcreteCoefficients.similarity,similarity_grid P s t u j hs hst,
      similarity_grid P s t u k hs hst]
    push_cast
    by_cases hk0 : similarityGridNumerator P s t u k = 0
    · simp [hk0]
    · have hK : (similarityGridNumerator P s t u k : ℚ) ≠ 0 := by exact_mod_cast hk0
      field_simp
  rw [he,rationalWord_nat_ratio]

theorem naturalDistance_eq_natAbs (j k : ℕ) :
    PhaseCellRationalArgs.naturalDistance j k = ((k : ℤ)-(j : ℤ)).natAbs := by
  by_cases hjk : j ≤ k
  · rw [← Nat.cast_sub hjk,Int.natAbs_natCast]
    simp [PhaseCellRationalArgs.naturalDistance,Nat.sub_eq_zero_of_le hjk]
  · have hkj : k ≤ j := by omega
    rw [show (k : ℤ)-(j : ℤ) = -((j-k : ℕ) : ℤ) by rw [Nat.cast_sub hkj]; ring,
      Int.natAbs_neg,Int.natAbs_natCast]
    simp [PhaseCellRationalArgs.naturalDistance,Nat.sub_eq_zero_of_le hkj]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
