module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorTapeCost

/-! Descriptor schedules pay their serialized data volume structurally, without
expanding a concrete packet bank or comparing register placements. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host
variable {N T A : ℕ} {β : Type}

theorem placedDescriptorTape_length (work : Fin N → Fin T) (words : Fin N → List (Fin (A+4))) :
    (descriptorBankTape (placedDescriptorFields work words)).length = 2*(∑ i, (words i).length)+N := by
  rw [descriptorBankTape_length]
  simp only [placedDescriptorFields,List.map_ofFn,Function.comp_def,List.sum_ofFn,List.length_ofFn]

theorem descriptorScheduleTape_length (work : Fin N → Fin T)
    (words : β → Fin N → List (Fin (A+4))) (records : List β) :
    (descriptorScheduleTape work words records).length =
      (records.map fun r => 2*(∑ i, (words r i).length)+N).sum := by
  induction records with
  | nil => rfl
  | cons r records ih =>
    change (descriptorBankTape (placedDescriptorFields work (words r))++
      descriptorScheduleTape work words records).length = _
    rw [List.length_append,placedDescriptorTape_length,ih]
    rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
