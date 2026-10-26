module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithinCoefficientHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedCoefficientAccuracy

/-! The emitted within-cell word has the original selected coefficient's grid
error. Selected geometric budgets also give its storage bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

theorem within_coefficient_error (q P s t u band : ℕ) (j k : ℤ) :
    |(value q (rationalWord q (PhaseCellConcreteCoefficients.entry P s t u band j k))).re-
      (PhaseCellConcreteCoefficients.entry P s t u band j k : ℝ)| ≤ 1/(2 : ℝ)^q :=
  rationalWord_error q _

theorem selected_within_coefficient_norm {s t u p q band : ℕ} {α d : ℝ} (j k : ℤ)
    (hp : 0 < p) (hs : 0 < s) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p) :
    ‖value q (rationalWord q (PhaseCellConcreteCoefficients.entry (2^15*p) s t u band j k))‖ ≤
      (2 : ℝ)^(8*p+1) := by
  have hP := (PhaseCellConcreteCoefficients.selected_precision p hp).1
  obtain ⟨hkj,hkone⟩ := PhaseCellConcreteCoefficients.selected_similarity_range k hp hs hαu hθ hgap hbudget
  obtain ⟨hjj,hjone⟩ := PhaseCellConcreteCoefficients.selected_similarity_range j hp hs hαu hθ hgap hbudget
  have hkpos : (0 : ℝ) < PhaseCellConcreteCoefficients.similarity (2^15*p) s t u k :=
    lt_of_lt_of_le (by positivity) hkj
  have hjpos : (0 : ℝ) < PhaseCellConcreteCoefficients.similarity (2^15*p) s t u j :=
    lt_of_lt_of_le (by positivity) hjj
  have hg := (PhaseCellConcreteCoefficients.gaussianArg s t u (k-j)).value_spec (2^15*p) hP
  have hgle := hg.2.1.trans (PhaseCellConcreteCoefficients.gaussianArg s t u (k-j)).target_bounds.2
  have hentry : 0 ≤ (PhaseCellConcreteCoefficients.entry (2^15*p) s t u band j k : ℝ) ∧
      (PhaseCellConcreteCoefficients.entry (2^15*p) s t u band j k : ℝ) ≤ (2 : ℝ)^(8*p+1) := by
    by_cases hjk : j = k
    · subst k
      simp [PhaseCellConcreteCoefficients.entry,PhaseCellExecutableCoefficients.entry]
      exact_mod_cast (Nat.one_le_two_pow (n := 8*p+1))
    · by_cases hb : (k-j).natAbs ≤ band
      · have hδ : k-j ≠ 0 := sub_ne_zero.mpr (Ne.symm hjk)
        simp only [PhaseCellConcreteCoefficients.entry,PhaseCellExecutableCoefficients.entry,
          if_neg hjk,PhaseCellExecutableCoefficients.kernel,if_neg hδ,if_pos hb,
          Rat.cast_mul,Rat.cast_div]
        simp only [mul_div_right_comm]
        change 0 ≤ ((PhaseCellConcreteCoefficients.similarity (2^15*p) s t u j : ℝ)/
          PhaseCellConcreteCoefficients.similarity (2^15*p) s t u k) *
          ((PhaseCellConcreteCoefficients.gaussianArg s t u (k-j)).value (2^15*p) : ℝ) ∧ _
        constructor
        · exact mul_nonneg (div_nonneg hjpos.le hkpos.le) hg.1
        · calc
            _ ≤ (1/(PhaseCellConcreteCoefficients.similarity (2^15*p) s t u k : ℝ))*1 :=
              mul_le_mul (div_le_div_of_nonneg_right hjone hkpos.le) hgle hg.1 (by positivity)
            _ ≤ (2 : ℝ)^(8*p+1) := by
              rw [mul_one]
              apply (div_le_iff₀ hkpos).mpr
              have hh := mul_le_mul_of_nonneg_left hkj (by positivity : (0 : ℝ) ≤ 2^(8*p+1))
              simpa only [mul_one_div_cancel (by positivity : (2 : ℝ)^(8*p+1) ≠ 0)] using hh
      · have hδ : k-j ≠ 0 := sub_ne_zero.mpr (Ne.symm hjk)
        simpa [PhaseCellConcreteCoefficients.entry,PhaseCellExecutableCoefficients.entry,hjk,
          PhaseCellExecutableCoefficients.kernel,hδ,hb] using
          (show (0 : ℝ) ≤ 2^(8*p+1) by positivity)
  have heQ : 0 ≤ PhaseCellConcreteCoefficients.entry (2^15*p) s t u band j k := by exact_mod_cast hentry.1
  rw [rationalWord_norm,abs_of_nonneg (rationalWord_nonneg q _ heQ)]
  exact (rationalWord_bounds q _).1.trans hentry.2

theorem selected_within_coefficient_fits {s t u p q band w : ℕ} {α d : ℝ} (j k : ℤ)
    (hp : 0 < p) (hs : 0 < s) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p) (hw : q+(8*p+1)+2 ≤ w) :
    Fits w (rationalWord q (PhaseCellConcreteCoefficients.entry (2^15*p) s t u band j k)) := by
  exact fits_of_value_power hw _
    (selected_within_coefficient_norm j k hp hs hαu hθ hgap hbudget)

theorem lifted_within_coefficient_error {s band i d : ℕ} (negative : Bool) (q P t u : ℕ)
    (hs : 0 < s) (hd : d ≤ band)
    (hphase : PhaseCellCrossCell.phaseQ s t i =
      PhaseCellCrossCell.phaseQ s t ((i : ℤ)+PhaseCellRationalArgs.couplingOffset negative d)) :
    |(value q (rationalWord q (PhaseCellConcreteCoefficients.entry P s t u band
      (PhaseCellRationalArgs.liftedSource s band i)
      (PhaseCellRationalArgs.liftedTarget negative s band i d)))).re-
      (PhaseCellCrossCell.entry P s t u band i
        ((i : ℤ)+PhaseCellRationalArgs.couplingOffset negative d) : ℝ)| ≤ 1/(2 : ℝ)^q := by
  have hphase' := (lifted_phase_eq_iff negative t hs hd).mpr hphase
  have he : PhaseCellCrossCell.entry P s t u band
      (PhaseCellRationalArgs.liftedSource s band i)
      (PhaseCellRationalArgs.liftedTarget negative s band i d) =
      PhaseCellConcreteCoefficients.entry P s t u band
      (PhaseCellRationalArgs.liftedSource s band i)
      (PhaseCellRationalArgs.liftedTarget negative s band i d) := by
    simp only [PhaseCellCrossCell.entry,if_pos hphase']
  rw [← he,PhaseCellRationalArgs.lifted_entry negative P t u hs hd]
  exact rationalWord_error q _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
