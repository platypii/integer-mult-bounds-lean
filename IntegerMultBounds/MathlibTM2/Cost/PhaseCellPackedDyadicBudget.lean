module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicCoefficientTranspose
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellStreamedDyadicTransposeBudget

/-! The actual packed router's complete bill: two time charges but one shared
routing reserve, plus linear codec and consuming-counter work. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open FixedStreamedBank
variable {Q : ℕ}

theorem restoringTimeCost_le (hstates : FixedStreamedBank.stateCount ≤ Q)
    (a b C V : ℕ) (hb : 0 < b) (hC : 0 < C) (hwidth : V ≤ 2^a*2^b*C) :
    (restoringTimeCost hstates a b C V : ℝ) ≤ (116*V+143+32921*(V+1)^5 : ℕ)+
      (generatedDyadicStageCoeff tapeCount 6 1+300)*(2^a*2^b*C : ℕ)*
        ((a : ℝ)/b*((b : ℝ)^Parameters.tau+1)+4*b)+2 := by
  have hh := canonicalDyadicScheduleTime_le (bank hstates) (a+b) a b C V 1 (2^a*2^b*C)
    hb (by omega) hC (by omega) hwidth
  unfold restoringTimeCost
  push_cast only [Nat.cast_add]
  linarith only [hh]

theorem packedDyadicTimeCost_le (hstates : FixedStreamedBank.stateCount ≤ Q)
    (a b C V : ℕ) (hb : 0 < b) (hC : 0 < C) (hwidth : V ≤ 2^a*2^b*C) :
    (26*(2^a*(2^b*C))+24+2*restoringTimeCost hstates a b C V : ℝ) ≤
      (26*(2^a*(2^b*C))+28+2*(116*V+143+32921*(V+1)^5) : ℕ)+
        2*(generatedDyadicStageCoeff tapeCount 6 1+300)*(2^a*2^b*C : ℕ)*
          ((a : ℝ)/b*((b : ℝ)^Parameters.tau+1)+4*b) := by
  have hh := restoringTimeCost_le hstates a b C V hb hC hwidth
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
  linarith only [hh]

theorem packedDyadicStockAllowance_le (hstates : FixedStreamedBank.stateCount ≤ Q)
    (a b C V : ℕ) (hC : 0 < C) (hwidth : V ≤ 2^a*2^b*C) :
    40*(2^a*(2^b*C))+38+restoringStockAllowance hstates a b C V ≤
      (342*V+423+98763*(V+1)^5)+(streamedDyadicStockCoeff tapeCount+40)*(2^a*2^b*C)+38 := by
  have hh := dyadicTransposeScheduleStock_le (bank hstates)
    (dyadicTransposePlan (a+b) a b C (by omega)) V hC hwidth
  unfold restoringStockAllowance
  nlinarith only [hh]

end IntegerMultBounds.MathlibTM2.Cost
