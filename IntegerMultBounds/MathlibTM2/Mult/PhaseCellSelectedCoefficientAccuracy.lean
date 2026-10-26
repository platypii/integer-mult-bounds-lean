module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithinCoefficientAccuracy

/-! One selected magnitude bound covers both numerical branches and diagonal. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

theorem selected_coefficient_norm {s t u p q band : ℕ} {α d : ℝ} (j k : ℤ)
    (hp : 0 < p) (hs : 0 < s) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p) :
    ‖value q (rationalWord q (PhaseCellCrossCell.entry (2^15*p) s t u band j k))‖ ≤
      (2 : ℝ)^(8*p+1) := by
  by_cases hphase : PhaseCellCrossCell.phaseQ s t j = PhaseCellCrossCell.phaseQ s t k
  · simpa only [PhaseCellCrossCell.entry,if_pos hphase] using
      selected_within_coefficient_norm (q := q) (band := band) j k hp hs hαu hθ hgap hbudget
  · simp only [PhaseCellCrossCell.entry,if_neg hphase]
    by_cases hband : (k-j).natAbs ≤ band
    · rw [if_pos hband]
      have hP := (PhaseCellConcreteCoefficients.selected_precision p hp).1
      have hdirect := (PhaseCellConcreteCoefficients.encode
        (PhaseCellCrossCell.latticeQ s t u j (k-j))).value_spec (2^15*p) hP
      have hnonneg : 0 ≤ PhaseCellCrossCell.direct (2^15*p) s t u j k := by
        exact_mod_cast hdirect.1
      rw [rationalWord_norm,abs_of_nonneg (rationalWord_nonneg q _ hnonneg)]
      apply (rationalWord_bounds q _).1.trans
      apply (hdirect.2.1.trans (PhaseCellConcreteCoefficients.encode
        (PhaseCellCrossCell.latticeQ s t u j (k-j))).target_bounds.2).trans
      exact_mod_cast (Nat.one_le_two_pow (n := 8*p+1))
    · simp only [if_neg hband]
      rw [rationalWord_norm]
      have hz : (value q (rationalWord q 0)).re = 0 := by simp [rationalWord,value]
      rw [hz,abs_zero]
      positivity

theorem selected_coefficient_fits {s t u p q band w : ℕ} {α d : ℝ} (j k : ℤ)
    (hp : 0 < p) (hs : 0 < s) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : α^2*d ≤ p) (hw : q+(8*p+1)+2 ≤ w) :
    Fits w (rationalWord q (PhaseCellCrossCell.entry (2^15*p) s t u band j k)) := by
  exact fits_of_value_power hw _ (selected_coefficient_norm j k hp hs hst hαu hθ hgap hbudget)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
