module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedDyadicStage
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDyadicTransposeCharge

/-! Complete generated-stage traffic over the exact rectangular schedule.
Bank contents and dimension-master preparation remain explicit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem sum_map_le_mul_sum {α : Type*} (rs : List α) (g f : α → ℝ) (C : ℝ)
    (h : ∀ r ∈ rs, g r ≤ C*f r) : (rs.map g).sum ≤ C*(rs.map f).sum := by
  revert h
  induction rs with
  | nil => intro h; simp
  | cons r rs ih =>
    intro h
    have hh := ih (by intro s hs; exact h s (by simp [hs]))
    have hr := h r (by simp)
    simp only [List.map_cons,List.sum_cons]
    nlinarith only [hr,hh]

theorem dyadicTransposeStageCosts_le {a b W T : ℕ}
    (plan : DyadicTransposePlan a b W) (dims : RectangularChunkSwap → Fin 5 → Fin T)
    (t₀ D stock : ℕ) (hW : 0 < W) (hstock : stock ≤ D*(2^a*2^b*W)) :
    (((plan.wiredStages dims).map (fun r =>
      generatedBalancedChunkInterchangeCost T t₀ r.outerCount r.blockWidth r.leftBits r.rightBits stock)).sum : ℝ) ≤
      generatedDyadicStageCoeff T t₀ D*(2^a*2^b*W : ℕ)*
        plan.weightedCharge (fun k => (k : ℝ)^Parameters.tau+1) := by
  have hh := sum_map_le_mul_sum (plan.wiredStages dims)
    (fun r => (generatedBalancedChunkInterchangeCost T t₀ r.outerCount r.blockWidth r.leftBits r.rightBits stock : ℝ))
    (fun r => (r.leftBits : ℝ)^Parameters.tau+1)
    (generatedDyadicStageCoeff T t₀ D*(2^a*2^b*W : ℕ)) (by
      intro r hr
      have hready := plan.wiredStages_ready dims hW r hr
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
      obtain ⟨k,hk,hbound,hl,hr⟩ := plan.stages_bits s hs
      have hv := plan.stages_volume s hs
      have hcost := generatedDyadicStageCost_le T t₀ D s.outerCount s.blockWidth k stock
        (2^a*2^b*W) hready.1.1 hready.1.2 hk
        (by simpa only [RectangularChunkSwap.volume,hl,hr] using hv.symm) hstock
      simpa only [hl,Nat.log_pow (by decide : 1 < 2)] using hcost)
  rw [plan.wiredStages_weightedCharge_eq dims (fun k => (k : ℝ)^Parameters.tau+1)] at hh
  simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using hh

theorem dyadicTransposeExactStageCosts_le (a b W T t₀ D stock : ℕ) (hb : 0 < b)
    (dims : RectangularChunkSwap → Fin 5 → Fin T) (hW : 0 < W)
    (hstock : stock ≤ D*(2^a*2^b*W)) :
    ((((dyadicTransposeExactPlan a b W hb).wiredStages dims).map (fun r =>
      generatedBalancedChunkInterchangeCost T t₀ r.outerCount r.blockWidth r.leftBits r.rightBits stock)).sum+1 : ℝ) ≤
      generatedDyadicStageCoeff T t₀ D*(2^a*2^b*W : ℕ)*
        ((a : ℝ)/b*((b : ℝ)^Parameters.tau+1)+4*b)+1 := by
  have hh := dyadicTransposeStageCosts_le (dyadicTransposeExactPlan a b W hb) dims t₀ D stock hW hstock
  have hc := dyadicTransposeExactPlan_rpowCharge_le a b W hb Parameters.tau tot_tau_le_one
  have hC : 0 ≤ generatedDyadicStageCoeff T t₀ D*(2^a*2^b*W : ℕ) := by
    unfold generatedDyadicStageCoeff
    have := Node.swapConst_pos
    positivity
  have hm := mul_le_mul_of_nonneg_left hc hC
  linarith only [hh,hm]

end IntegerMultBounds.MathlibTM2.Cost
