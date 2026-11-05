module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRetainedPublicationBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSymmetricRestoringBudget

/-! Publication uses the gather orientation's sharp charge on the same schedule.
Disjoint windows control padding before any selected geometry is instantiated. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open FixedStreamedBank

theorem publicationTransposeCosts_le {Q s L : ℕ}
    (hstates : FixedStreamedBank.stateCount ≤ Q) (windows : PublicationWindows s L)
    (hL : L ≤ s) (b W V : ℕ) (hpacket : 0 < L*W)
    (hwidth : V ≤ 2^Nat.clog 2 windows.origins.length*2^b*(L*W)) :
    let a := Nat.clog 2 windows.origins.length
    (restoringTimeCost hstates a b (L*W) V : ℝ) ≤
      (116*V+143+32921*(V+1)^5 : ℕ)+
      3*(generatedDyadicStageCoeff tapeCount 6 1+300)*(2^b*(s*W) : ℕ)*dyadicRouteCharge b a+2 ∧
    restoringStockAllowance hstates a b (L*W) V ≤
      (342*V+423+98763*(V+1)^5)+
      3*(streamedDyadicStockCoeff tapeCount+40)*(2^b*(s*W))+38 := by
  dsimp only
  let a := Nat.clog 2 windows.origins.length
  have hv := publicationPaddedVolume_le windows hL b W
  have ht := restoringTimeCost_swap_le hstates a b (L*W) V hpacket hwidth
  have hs := packedDyadicStockAllowance_le hstates a b (L*W) V hpacket hwidth
  have hcoeff : 0 ≤ generatedDyadicStageCoeff tapeCount 6 1+300 := by
    unfold generatedDyadicStageCoeff
    exact add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) Node.swapConst_pos.le)
      (Nat.cast_nonneg _)) (by norm_num)
  have hvR : (2^a*2^b*(L*W) : ℕ) ≤ (3 : ℝ)*(2^b*(s*W) : ℕ) := by
    exact_mod_cast hv
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvR hcoeff)
    (dyadicRouteCharge_nonneg b a)
  have hsVolume := Nat.mul_le_mul_left (streamedDyadicStockCoeff tapeCount+40) hv
  constructor
  · dsimp only [a] at ht hm
    nlinarith only [ht,hm]
  · dsimp only [a] at hs
    nlinarith only [hs,hsVolume,Nat.zero_le (40*(2^Nat.clog 2 windows.origins.length*(2^b*(L*W))))]

end IntegerMultBounds.MathlibTM2.Cost
