module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellStreamedDyadicBudget

/-! Sum the complete streamed bills along a structural transpose plan and
share the linear stock allowance across its stages. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem dyadicTransposeScheduleTime_le {a b C t₀ T Q : ℕ}
    (bank : StreamedChunkBank t₀ T Q) (plan : DyadicTransposePlan a b C)
    (wordWidth D stock : ℕ) (hC : 0 < C) (hstock : stock ≤ D*(2^a*2^b*C))
    (hwidth : wordWidth ≤ 2^a*2^b*C) :
    (((plan.wiredStages (fun _ => bank.dims)).map (fun r => bank.stageTimeCost wordWidth stock r+3)).sum : ℝ) ≤
      (generatedDyadicStageCoeff T t₀ D+300)*(2^a*2^b*C : ℕ)*
        plan.weightedCharge (fun k => (k : ℝ)^Parameters.tau+1) := by
  have hh := sum_map_le_mul_sum (plan.wiredStages (fun _ => bank.dims))
    (fun r => (bank.stageTimeCost wordWidth stock r+3 : ℝ))
    (fun r => (r.leftBits : ℝ)^Parameters.tau+1)
    ((generatedDyadicStageCoeff T t₀ D+300)*(2^a*2^b*C : ℕ)) (by
      intro r hr
      have hready := plan.wiredStages_ready (fun _ => bank.dims) hC r hr
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
      obtain ⟨k,hk,hbound,hl,hr⟩ := plan.stages_bits s hs
      have hv := plan.stages_volume s hs
      have hc := streamedDyadicStageTime_le bank wordWidth D s.outerCount s.blockWidth k stock
        (2^a*2^b*C) hready.1.1 hready.1.2 hk
        (by simpa only [RectangularChunkSwap.volume,hl,hr] using hv.symm) hstock hwidth
      simpa only [hl,Nat.log_pow (by decide : 1 < 2)] using hc)
  rw [plan.wiredStages_weightedCharge_eq (fun _ => bank.dims) (fun k => (k : ℝ)^Parameters.tau+1)] at hh
  simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def,Nat.cast_add,Nat.cast_ofNat] using hh

theorem dyadicTransposeScheduleStock_le {a b C t₀ T Q : ℕ}
    (bank : StreamedChunkBank t₀ T Q) (plan : DyadicTransposePlan a b C)
    (wordWidth : ℕ) (hC : 0 < C) (hwidth : wordWidth ≤ 2^a*2^b*C) :
    bank.scheduleStockAllowance wordWidth (plan.wiredStages (fun _ => bank.dims)) ≤
      streamedDyadicStockCoeff T*(2^a*2^b*C) := by
  have hall : ∀ r ∈ plan.wiredStages (fun _ => bank.dims), bank.stageStockAllowance wordWidth r ≤
      streamedDyadicStockCoeff T*(2^a*2^b*C) := by
    intro r hr
    have hready := plan.wiredStages_ready (fun _ => bank.dims) hC r hr
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    obtain ⟨k,hk,hbound,hl,hr⟩ := plan.stages_bits s hs
    have hv := plan.stages_volume s hs
    have hc := streamedDyadicStageStock_le bank wordWidth s.outerCount s.blockWidth k (2^a*2^b*C)
      hready.1.1 hready.1.2 (by simpa only [RectangularChunkSwap.volume,hl,hr] using hv.symm) hwidth
    simpa only [hl,Nat.log_pow (by decide : 1 < 2)] using hc
  have hmax : ∀ rs : List (BalancedChunkInterchangeStage T),
      (∀ r ∈ rs, bank.stageStockAllowance wordWidth r ≤ streamedDyadicStockCoeff T*(2^a*2^b*C)) →
      bank.scheduleStockAllowance wordWidth rs ≤ streamedDyadicStockCoeff T*(2^a*2^b*C) := by
    intro rs
    induction rs with
    | nil => intro h; exact Nat.zero_le _
    | cons r rs ih =>
      intro h
      exact max_le (h r (by simp)) (ih (by intro s hs; exact h s (by simp [hs])))
  exact hmax _ hall

theorem canonicalDyadicScheduleTime_le {t₀ T Q : ℕ} (bank : StreamedChunkBank t₀ T Q)
    (fuel a b C wordWidth D stock : ℕ) (hb : 0 < b) (h : a+b ≤ fuel) (hC : 0 < C)
    (hstock : stock ≤ D*(2^a*2^b*C)) (hwidth : wordWidth ≤ 2^a*2^b*C) :
    ((((dyadicTransposePlan fuel a b C h).wiredStages (fun _ => bank.dims)).map
      (fun r => bank.stageTimeCost wordWidth stock r+3)).sum+2 : ℝ) ≤
      (generatedDyadicStageCoeff T t₀ D+300)*(2^a*2^b*C : ℕ)*
        ((a : ℝ)/b*((b : ℝ)^Parameters.tau+1)+4*b)+2 := by
  have hh := dyadicTransposeScheduleTime_le bank (dyadicTransposePlan fuel a b C h)
    wordWidth D stock hC hstock hwidth
  have hc := dyadicTransposePlan_rpowCharge_le fuel a b C hb h Parameters.tau tot_tau_le_one
  have hcoeff : 0 ≤ (generatedDyadicStageCoeff T t₀ D+300)*(2^a*2^b*C : ℕ) := by
    unfold generatedDyadicStageCoeff
    have := Node.swapConst_pos
    positivity
  have hm := mul_le_mul_of_nonneg_left hc hcoeff
  linarith only [hh,hm]

end IntegerMultBounds.MathlibTM2.Cost
