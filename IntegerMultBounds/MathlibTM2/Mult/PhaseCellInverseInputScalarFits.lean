module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedInverseCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseScalarSetup

/-! Scalar-table fits shared by inverse header generation and final rounding. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {A : ℕ}

theorem inverseInputScalars_fit {W p u l target s t a b : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^W) :
    ∀ i, (inverseInputScalars (A := A) p u l target s t a b).val i < 2^W := by
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  have hroom : 2^15*(p+1)+8*E+2*((haloBoundary s t (PhaseCellBand.width p u) a b).card+1)+
      4*(PhaseCellBand.width p u+1)+9 < 2^W := hprecisionRoom
  have hEl : 2*l+target ≤ E := by dsimp [E,inverseExecutionExponent]; omega
  have htW : t < 2^W := by nlinarith only [hgeometryRoom,Nat.zero_le (t*t)]
  have hsW : s < 2^W := by omega
  intro i
  fin_cases i <;> simp [inverseInputScalars] <;> omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
