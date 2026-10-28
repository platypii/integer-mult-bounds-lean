module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatch

/-! The counted loop and exact tape/count restoration cost a fixed multiple of its real dispatch steps. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN

theorem familyDispatchInput_restore_le_cost {T A s : ℕ} [NeZero s]
    (p l t : ℕ) (work : Fin 303 → Fin T) (r : FamilyDispatchInput s A) :
    2*(descriptorBankTape (placedDescriptorFields work r.words)).length+9 ≤ r.cost p l t work := by
  rw [descriptorBankTape_length]
  simp only [placedDescriptorFields,List.map_ofFn,Function.comp_def,List.sum_ofFn,List.length_ofFn]
  unfold FamilyDispatchInput.cost physicalFamilyDispatchCost
  rw [takePlacedDescriptorBankCost_eq]
  dsimp only
  omega

theorem familyDispatch_restore_ledger_le {T A s : ℕ} [NeZero s]
    (p l t : ℕ) (work : Fin 303 → Fin T) (records : List (FamilyDispatchInput s A)) :
    (records.map (fun r => r.cost p l t work+3)).sum+6*records.length+
        2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 ≤
      2*(records.map (fun r => r.cost p l t work)).sum+10 := by
  induction records with
  | nil => simp [descriptorScheduleTape]
  | cons r records ih =>
    have hc := familyDispatchInput_restore_le_cost p l t work r
    change (records.map (fun r => r.cost p l t work+3)).sum+6*records.length+
        2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 ≤
      2*(records.map (fun r => r.cost p l t work)).sum+10 at ih
    simp only [List.map_cons,List.sum_cons,List.length_cons,descriptorScheduleTape,
      List.flatMap_cons,List.length_append] at ih ⊢
    omega

end IntegerMultBounds.MathlibTM2.Cost
