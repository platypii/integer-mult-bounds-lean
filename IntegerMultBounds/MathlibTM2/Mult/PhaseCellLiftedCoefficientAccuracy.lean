module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedCoefficientFromHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDirectCoefficientAccuracy

/-! The emitted lifted coefficient approximates the original signed-offset
entry. Lifting changes neither the phase decision nor the retained band test. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

theorem lifted_phase_eq_iff {s band i d : ℕ} (negative : Bool) (t : ℕ)
    (hs : 0 < s) (hd : d ≤ band) :
    PhaseCellCrossCell.phaseQ s t (liftedSource s band i) =
      PhaseCellCrossCell.phaseQ s t (liftedTarget negative s band i d) ↔
    PhaseCellCrossCell.phaseQ s t i = PhaseCellCrossCell.phaseQ s t ((i : ℤ)+couplingOffset negative d) := by
  rw [liftedSource_cast,liftedTarget_cast negative hs hd,
    show (i : ℤ)+(band : ℤ)*s+couplingOffset negative d =
      ((i : ℤ)+couplingOffset negative d)+(band : ℤ)*s by ring,
    PhaseCellCrossCell.phaseQ_period s t hs,PhaseCellCrossCell.phaseQ_period s t hs]
  exact add_right_cancel_iff

theorem lifted_cross_coefficient_error {s band i d : ℕ} (negative : Bool) (q P t u : ℕ)
    (hs : 0 < s) (hd : d ≤ band)
    (hphase : PhaseCellCrossCell.phaseQ s t i ≠
      PhaseCellCrossCell.phaseQ s t ((i : ℤ)+couplingOffset negative d)) :
    |(value q (rationalWord q (PhaseCellCrossCell.direct P s t u
      (liftedSource s band i) (liftedTarget negative s band i d)))).re-
      (PhaseCellCrossCell.entry P s t u band i ((i : ℤ)+couplingOffset negative d) : ℝ)| ≤
        1/(2 : ℝ)^q := by
  have hphase' : PhaseCellCrossCell.phaseQ s t (liftedSource s band i) ≠
      PhaseCellCrossCell.phaseQ s t (liftedTarget negative s band i d) :=
    fun h => hphase ((lifted_phase_eq_iff negative t hs hd).mp h)
  have hband : ((liftedTarget negative s band i d : ℤ)-(liftedSource s band i : ℤ)).natAbs ≤ band := by
    rw [liftedTarget_cast negative hs hd,liftedSource_cast,
      show ((i : ℤ)+(band : ℤ)*s+couplingOffset negative d)-((i : ℤ)+(band : ℤ)*s) =
        couplingOffset negative d by ring]
    cases negative <;> simpa [couplingOffset] using hd
  have hh := cross_coefficient_error q P s t u band (liftedSource s band i)
    (liftedTarget negative s band i d) hphase' hband
  rw [lifted_entry negative P t u hs hd] at hh
  exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
