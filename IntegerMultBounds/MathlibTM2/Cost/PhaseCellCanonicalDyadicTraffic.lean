module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCanonicalDyadicCharge
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDyadicTransposeTraffic

/-! Sharp physical stage traffic for the canonical schedule emitted by the
fixed arithmetic selector. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem dyadicTransposeCanonicalStageCosts_le (fuel a b W T t₀ D stock : ℕ)
    (hb : 0 < b) (h : a+b ≤ fuel)
    (dims : RectangularChunkSwap → Fin 5 → Fin T) (hW : 0 < W)
    (hstock : stock ≤ D*(2^a*2^b*W)) :
    ((((dyadicTransposePlan fuel a b W h).wiredStages dims).map (fun r =>
      generatedBalancedChunkInterchangeCost T t₀ r.outerCount r.blockWidth r.leftBits r.rightBits stock)).sum+1 : ℝ) ≤
      generatedDyadicStageCoeff T t₀ D*(2^a*2^b*W : ℕ)*
        ((a : ℝ)/b*((b : ℝ)^Parameters.tau+1)+4*b)+1 := by
  have hh := dyadicTransposeStageCosts_le (dyadicTransposePlan fuel a b W h) dims t₀ D stock hW hstock
  have hc := dyadicTransposePlan_rpowCharge_le fuel a b W hb h Parameters.tau tot_tau_le_one
  have hC : 0 ≤ generatedDyadicStageCoeff T t₀ D*(2^a*2^b*W : ℕ) := by
    unfold generatedDyadicStageCoeff
    have := Node.swapConst_pos
    positivity
  have hm := mul_le_mul_of_nonneg_left hc hC
  linarith only [hh,hm]

end IntegerMultBounds.MathlibTM2.Cost
