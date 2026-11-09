module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightPrepare
import Mathlib.Tactic.Ring

/-! Scalar-counter construction has an explicit encoded-width cost. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem scalarBankLoadCost_eq (w : ℕ) :
    chirpBankLoadCost bank bankInput w w (inputBits w) = 42*w+49 := by
  simp [chirpBankLoadCost,chirpBankCopiesCost,chirpBankInputAssignments,
    bankInput,inputBits,List.ofFn_succ]
  omega

theorem prepareCost_le_width (q w : ℕ) (hq : q ≤ w) :
    prepareCost q w ≤
      20000*((2*w).size+1)*(w+1)^2+6*IntegerMultBounds.Schoenhage.Schedule.topN w := by
  unfold prepareCost counterSetupCost
  rw [scalarBankLoadCost_eq]
  unfold chirpMultiplierSetupCost tblC
  have hmul := Nat.mul_le_mul_right w hq
  ring_nf at hmul ⊢
  omega

theorem prepareWeightsCost_le_width (q b w : ℕ) (hqb : q+b ≤ w) :
    prepareWeightsCost q b w ≤
      20020*((2*w).size+1)*(w+1)^2+6*IntegerMultBounds.Schoenhage.Schedule.topN w := by
  have h := prepareCost_le_width (q+b) w hqb
  have hb : b ≤ w := by omega
  unfold prepareWeightsCost
  ring_nf at h ⊢
  omega

theorem prepareCost_le_header_square (q w : ℕ) (hw : 1 ≤ w) (hq : q ≤ w) :
    prepareCost q w ≤ 20100*((2*w).size+1)*(w+1)^2 := by
  have h := prepareCost_le_width q w hq
  have ht := (IntegerMultBounds.Schoenhage.Schedule.topN_facts hw).2.1
  ring_nf at h ⊢
  omega

theorem prepareWeightsCost_le_header_square (q b w : ℕ) (hw : 1 ≤ w) (hqb : q+b ≤ w) :
    prepareWeightsCost q b w ≤ 20100*((2*w).size+1)*(w+1)^2 := by
  have h := prepareWeightsCost_le_width q b w hqb
  have ht := (IntegerMultBounds.Schoenhage.Schedule.topN_facts hw).2.1
  ring_nf at h ⊢
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
