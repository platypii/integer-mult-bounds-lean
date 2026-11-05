module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSymmetricDyadicCharge
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellTotalDyadicBudget

/-! The same physical restoring transpose admits the charge of either axis. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open FixedStreamedBank

theorem restoringTimeCost_swap_le {Q : ℕ} (hstates : FixedStreamedBank.stateCount ≤ Q)
    (a b C V : ℕ) (hC : 0 < C) (hwidth : V ≤ 2^a*2^b*C) :
    (restoringTimeCost hstates a b C V : ℝ) ≤ (116*V+143+32921*(V+1)^5 : ℕ)+
      (generatedDyadicStageCoeff tapeCount 6 1+300)*(2^a*2^b*C : ℕ)*dyadicRouteCharge b a+2 := by
  by_cases ha : a = 0
  · subst a
    cases b <;> simp [restoringTimeCost,dyadicTransposePlan,DyadicTransposePlan.wiredStages,
      DyadicTransposePlan.stages,dyadicRouteCharge]
  have hh := dyadicTransposeScheduleTime_le (bank hstates)
    (dyadicTransposePlan (a+b) a b C (by omega)) V 1 (2^a*2^b*C) hC (by omega) hwidth
  rw [dyadicTransposePlan_weightedCharge_swap] at hh
  have hc := dyadicTransposePlan_rpowCharge_le (a+b) b a C (by omega) (by omega)
    Parameters.tau tot_tau_le_one
  have hcoeff : 0 ≤ (generatedDyadicStageCoeff tapeCount 6 1+300)*(2^a*2^b*C : ℕ) := by
    unfold generatedDyadicStageCoeff
    have := Node.swapConst_pos
    positivity
  have hm := mul_le_mul_of_nonneg_left hc hcoeff
  unfold restoringTimeCost
  simp only [dyadicRouteCharge,ite_eq_right ha]
  push_cast only [Nat.cast_add,Nat.cast_ofNat]
  linarith only [hh,hm]

end IntegerMultBounds.MathlibTM2.Cost
