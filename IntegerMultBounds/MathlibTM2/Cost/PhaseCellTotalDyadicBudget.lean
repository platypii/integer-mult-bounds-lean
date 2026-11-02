module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedDyadicBudget

/-! The sharp dyadic charge includes singleton key axes: their schedule is
empty and their charge is zero. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open FixedStreamedBank
variable {Q : ℕ}

noncomputable def dyadicRouteCharge (a b : ℕ) : ℝ :=
  if b = 0 then 0 else (a : ℝ)/b*((b : ℝ)^Parameters.tau+1)+4*b

theorem dyadicRouteCharge_nonneg (a b : ℕ) : 0 ≤ dyadicRouteCharge a b := by
  unfold dyadicRouteCharge
  split_ifs <;> positivity

theorem dyadicTransposePlan_zeroRight_stages (a C : ℕ) :
    (dyadicTransposePlan a a 0 C (by omega)).stages = [] := by
  cases a with
  | zero => rfl
  | succ a => simp [dyadicTransposePlan,DyadicTransposePlan.stages]

theorem restoringTimeCost_zeroRight (hstates : FixedStreamedBank.stateCount ≤ Q) (a C V : ℕ) :
    restoringTimeCost hstates a 0 C V = (116*V+143+32921*(V+1)^5)+2 := by
  simp [restoringTimeCost,DyadicTransposePlan.wiredStages,dyadicTransposePlan_zeroRight_stages]

theorem restoringTimeCost_total_le (hstates : FixedStreamedBank.stateCount ≤ Q)
    (a b C V : ℕ) (hC : 0 < C) (hwidth : V ≤ 2^a*2^b*C) :
    (restoringTimeCost hstates a b C V : ℝ) ≤ (116*V+143+32921*(V+1)^5 : ℕ)+
      (generatedDyadicStageCoeff tapeCount 6 1+300)*(2^a*2^b*C : ℕ)*dyadicRouteCharge a b+2 := by
  by_cases hb : b = 0
  · subst b
    simp [restoringTimeCost_zeroRight,dyadicRouteCharge]
  · simpa only [dyadicRouteCharge,if_neg hb] using
      restoringTimeCost_le hstates a b C V (by omega) hC hwidth

end IntegerMultBounds.MathlibTM2.Cost
