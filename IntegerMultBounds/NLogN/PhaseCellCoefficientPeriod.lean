module

public import IntegerMultBounds.NLogN.PhaseCellCrossCell

/-! Integer-period lifts preserve every selected coefficient, including the
phase decision. The ambient matrix is never restarted at a halo endpoint. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRationalArgs

theorem nearestQ_period (s t : ℕ) (hs : 0 < s) (j m : ℤ) :
    nearestQ s t (j+m*s) = nearestQ s t j+m*t := by
  unfold nearestQ
  rw [show 2*(t : ℤ)*(j+m*s)+s = (2*(t : ℤ)*j+s)+(m*t)*(2*s) by ring,
    Int.add_mul_ediv_right _ _ (by omega)]

theorem betaQ_period (s t : ℕ) (hs : 0 < s) (j m : ℤ) :
    betaQ s t (j+m*s) = betaQ s t j := by
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [betaQ,nearestQ_period s t hs,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  field_simp
  ring

theorem potentialQ_period (s t u : ℕ) (hs : 0 < s) (j m : ℤ) :
    potentialQ s t u (j+m*s) = potentialQ s t u j := by
  simp only [potentialQ,betaQ_period s t hs]

end IntegerMultBounds.NLogN.PhaseCellRationalArgs

namespace IntegerMultBounds.NLogN.PhaseCellCrossCell

open PhaseCellRationalArgs

theorem phaseQ_period (s t : ℕ) (hs : 0 < s) (j m : ℤ) :
    phaseQ s t (j+m*s) = phaseQ s t j+m*((t : ℤ)-s) := by
  rw [phaseQ,nearestQ_period s t hs,phaseQ]
  ring

theorem latticeQ_period (s t u : ℕ) (hs : 0 < s) (j δ m : ℤ) :
    latticeQ s t u (j+m*s) δ = latticeQ s t u j δ := by
  unfold latticeQ
  rw [betaQ_period s t hs,show j+m*s+δ = (j+δ)+m*s by ring,betaQ_period s t hs]

theorem direct_period (P s t u : ℕ) (hs : 0 < s) (j k m : ℤ) :
    direct P s t u (j+m*s) (k+m*s) = direct P s t u j k := by
  unfold direct
  rw [show (k+m*s)-(j+m*s) = k-j by ring,latticeQ_period s t u hs]

theorem entry_period (P s t u band : ℕ) (hs : 0 < s) (j k m : ℤ) :
    entry P s t u band (j+m*s) (k+m*s) = entry P s t u band j k := by
  simp only [entry,phaseQ_period s t hs,add_right_inj,direct_period P s t u hs,
    show (k+m*s)-(j+m*s) = k-j by ring]
  congr 1
  · apply propext
    constructor
    · exact add_right_cancel
    · intro h; rw [h]
  · simp only [PhaseCellConcreteCoefficients.entry,PhaseCellExecutableCoefficients.entry,
      PhaseCellConcreteCoefficients.similarityArg,PhaseCellRationalArgs.potentialQ_period s t u hs,
      add_right_cancel_iff,show (k+m*s)-(j+m*s) = k-j by ring]

end IntegerMultBounds.NLogN.PhaseCellCrossCell
