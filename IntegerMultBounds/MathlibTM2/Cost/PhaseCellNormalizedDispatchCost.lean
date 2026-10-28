module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellNormalizationCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedDispatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSchedule

/-! Reuse raw complete-key ledgers through fixed-factor normalized step bounds. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

variable {T s A : ℕ} [NeZero s]

theorem normalized_output_width_le (p l t : ℕ) (r : FamilyDispatchInput s A) :
    2*p+13 ≤ r.width p l t := by
  have h := r.round_dimensions p l t (inverseNormalizationShift p) (inverseNormalizationShift_le p)
  omega

theorem normalizedDispatchInput_cost_le (p l t : ℕ) (work : Fin 303 → Fin T) (r : FamilyDispatchInput s A) :
    r.normalizedCost p l t work ≤ 9*r.cost p l t work := by
  have hn := inverseRoundBatchCost_le_callerCost A (inverseCallerWordWidth p r.u l r.target s t)
    p r.u l r.target s t r.a r.b r.inputs.length
  have hw := normalized_output_width_le p l t r
  have hfinish := Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left (r.inputs.length*s) hw)
  dsimp only [FamilyDispatchInput.normalizedCost,normalizedFamilyInverseBatchCost,
    FamilyDispatchInput.cost,physicalFamilyDispatchCost]
  change _ ≤ 9*(takeDescriptorBankCost (placedDescriptorFields work r.words)+
    familyInverseBatchCallerCost A (inverseCallerWordWidth p r.u l r.target s t)
      p r.u l s t r.a r.b r.target r.inputs.length+
    (6*(r.inputs.length*s*r.width p l t)+2*(∑ i, (r.words i).length)+611))
  omega

theorem normalizedDispatchInput_stock_le (p l t : ℕ) (work : Fin 303 → Fin T) (r : FamilyDispatchInput s A) :
    r.normalizedStock p l t work ≤ 9*r.stock p l t work := by
  have hn := inverseRoundBatchCost_le_callerStock A (inverseCallerWordWidth p r.u l r.target s t)
    p r.u l r.target s t r.a r.b r.inputs.length
  have hw := normalized_output_width_le p l t r
  have hfinish := Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left (r.inputs.length*s) hw)
  dsimp only [FamilyDispatchInput.normalizedStock,normalizedFamilyInverseBatchStockCost,
    FamilyDispatchInput.stock]
  omega

theorem normalizedDispatch_time_ledger_le (p l t : ℕ) (work : Fin 303 → Fin T)
    (records : List (FamilyDispatchInput s A)) :
    (records.map (fun r => r.normalizedCost p l t work+3)).sum+6*records.length+
        2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 ≤
      9*((records.map (fun r => r.cost p l t work+3)).sum+6*records.length+
        2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10) := by
  have hs := List.sum_le_sum (l := records) (fun r _ =>
    show r.normalizedCost p l t work+3 ≤ 9*(r.cost p l t work+3) from by
      have h := normalizedDispatchInput_cost_le p l t work r
      omega)
  simp only [List.sum_map_mul_left] at hs
  omega

theorem normalizedDispatch_stock_ledger_le (p l t : ℕ) (work : Fin 303 → Fin T)
    (records : List (FamilyDispatchInput s A)) :
    (records.map (fun r => r.normalizedStock p l t work)).sum+6*records.length+
        2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+8 ≤
      9*((records.map (fun r => r.stock p l t work)).sum+6*records.length+
        2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+8) := by
  have hs := List.sum_le_sum (l := records) (fun r _ => normalizedDispatchInput_stock_le p l t work r)
  simp only [List.sum_map_mul_left] at hs
  change (records.map (fun r => r.normalizedStock p l t work)).sum ≤
    9*(records.map (fun r => r.stock p l t work)).sum at hs
  omega

end IntegerMultBounds.MathlibTM2.Cost
