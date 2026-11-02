module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedDyadicSchedule

/-! Uniform polynomial budget for recomputing the schedule rows. This pays
compiled table execution; publication and selected absorption are separate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem dyadicGeneratorAtoms_le (a b W : ℕ) (hbits : a+b < W) :
    dyadicStageCount (a+b) a b*((a+b)*(4*(a+b)+19)+27)+13 ≤ 63*(W+1)^3 := by
  have hN := dyadicStageCount_le (a+b) a b (by omega)
  have hB : a+b ≤ W+1 := by omega
  have hB2 := Nat.pow_le_pow_left hB 2
  have hinner : (a+b)*(4*(a+b)+19)+27 ≤ 50*(W+1)^2 := by
    nlinarith only [hB,hB2]
  have hprod := Nat.mul_le_mul (hN.trans hB) hinner
  have hcube : 1 ≤ (W+1)^3 := by
    have : 0 < (W+1)^3 := by positivity
    omega
  nlinarith only [hprod,hcube]

theorem dyadicGeneratorCompiledTime_le (a b W : ℕ) (hbits : a+b < W) :
    (dyadicStageCount (a+b) a b*((a+b)*(4*(a+b)+19)+27)+13)*tblC W W ≤
      32760*(W+1)^5 := by
  have hC : tblC W W ≤ 520*(W+1)^2 := by
    unfold tblC
    nlinarith
  have hh := Nat.mul_le_mul (dyadicGeneratorAtoms_le a b W hbits) hC
  nlinarith only [hh]

/-- Include unary stage-count export, binary publication and bank release. -/
theorem dyadicGeneratorPublicationTime_le (a b W : ℕ) (hbits : a+b < W) :
    (dyadicStageCount (a+b) a b*((a+b)*(4*(a+b)+19)+27)+13)*tblC W W+
      (10*dyadicStageCount (a+b) a b+73)*W+6*dyadicStageCount (a+b) a b+72 ≤
      32921*(W+1)^5 := by
  have hN : dyadicStageCount (a+b) a b ≤ W :=
    (dyadicStageCount_le (a+b) a b (by omega)).trans hbits.le
  have hmul := Nat.mul_le_mul_right W hN
  have hmeta : (10*dyadicStageCount (a+b) a b+73)*W+
      6*dyadicStageCount (a+b) a b+72 ≤ 161*(W+1)^2 := by
    nlinarith only [hN,hmul]
  have hpow : (W+1)^2 ≤ (W+1)^5 := pow_le_pow_right' (by omega) (by decide)
  have hcompiled := dyadicGeneratorCompiledTime_le a b W hbits
  nlinarith only [hcompiled,hmeta,hpow]

end IntegerMultBounds.MathlibTM2.Cost
