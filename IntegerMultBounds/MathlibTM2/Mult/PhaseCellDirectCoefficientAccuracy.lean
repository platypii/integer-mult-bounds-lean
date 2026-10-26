module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDirectCoefficientHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStream

/-! The generated direct coefficient approximates the selected original matrix
entry. Semantic sampling precision and arithmetic storage precision stay separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

theorem direct_coefficient_norm (q P s t u j k : ℕ) (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) :
    ‖value q (rationalWord q (PhaseCellCrossCell.direct P s t u j k))‖ ≤ 1 := by
  have hb : 0 < s^2 := by positivity
  have hh := PhaseCellExpSample.sample_spec P (latticeNumerator s t u j k) (s^2) hP hb
  have hexp : Real.exp (-(Real.pi*(latticeNumerator s t u j k : ℝ)/(s^2 : ℕ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply neg_nonpos.mpr
    positivity
  have hnonneg : 0 ≤ PhaseCellCrossCell.direct P s t u j k := by
    rw [direct_sample P s t u j k hs hst]
    exact PhaseCellExpSample.sample_nonneg _ _ _
  rw [rationalWord_norm,abs_of_nonneg (rationalWord_nonneg q _ hnonneg)]
  apply (rationalWord_bounds q _).1.trans
  rw [direct_sample P s t u j k hs hst]
  exact hh.2.1.trans hexp

theorem cross_coefficient_error (q P s t u band j k : ℕ)
    (hphase : PhaseCellCrossCell.phaseQ s t j ≠ PhaseCellCrossCell.phaseQ s t k)
    (hband : ((k : ℤ)-(j : ℤ)).natAbs ≤ band) :
    |(value q (rationalWord q (PhaseCellCrossCell.direct P s t u j k))).re-
      (PhaseCellCrossCell.entry P s t u band j k : ℝ)| ≤ 1/(2 : ℝ)^q := by
  rw [PhaseCellCrossCell.entry,if_neg hphase,if_pos hband]
  exact rationalWord_error q _

theorem cross_coefficient_fits {q w P s t u j k : ℕ}
    (hw : q+2 ≤ w) (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) :
    Fits w (rationalWord q (PhaseCellCrossCell.direct P s t u j k)) := by
  apply fits_of_value_power (e := 0) (by omega)
  simpa only [pow_zero] using direct_coefficient_norm q P s t u j k hP hs hst

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
