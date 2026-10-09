import IntegerMultBounds.Machine.ActivePrefixStageRuntimeWord
import IntegerMultBounds.Networks.BinaryRowColumns
import IntegerMultBounds.Machine.CompactBinaryBasisSchedule

/-! Actual runtime address destinations perform the literal binary row
addition on every selected column, retaining every other original slot. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (geometry Address)
open ActivePrefixStageRuntimeSelected (destination)
open ActivePrefixStageRuntimeWord
open ActivePrefixStageParameters ActivePrefixStageGeometry
open Networks.BinaryRowProgram (Op)
variable {s : Shape}

def op (d : Inputs s) : Op (Fin d.stage.slots) :=
  {source:=d.stage.source,target:=d.stage.target,distinct:=d.stage.distinct.symm}

def coordinates (d : Inputs s) (i : Address d) : Fin d.stage.f → Fin d.stage.slots → Bool :=
  fun axis slot => (word d i).getD (slotLow d.stage slot+(d.stage.rho+axis.val*s.chunk)) false

theorem lower_slot (v : Stage s) (a b : Fin v.slots) (h : a.val<b.val) :
    slotLow v b+v.f*s.chunk≤slotLow v a := by
  have hc : v.slots-b.val-1+1≤v.slots-a.val-1 := by have := b.isLt; omega
  have hm := Nat.mul_le_mul_right v.f hc
  simp only [Nat.add_mul,Nat.one_mul] at hm
  have hh : lowAxes v b+v.f≤lowAxes v a := by unfold lowAxes; omega
  have hk := Nat.mul_le_mul_right s.chunk hh
  simpa only [Nat.add_mul,slotLow] using hk

theorem other_position (d : Inputs s) (slot : Fin d.stage.slots) (axis : Fin d.stage.f)
    (h : slot≠d.stage.target) :
    slotLow d.stage slot+(d.stage.rho+axis.val*s.chunk)<(geometry d).after ∨
    (geometry d).after+(geometry d).n*(geometry d).q+1≤
      slotLow d.stage slot+(d.stage.rho+axis.val*s.chunk) := by
  have hd : slot.val≠d.stage.target.val := fun he => h (Fin.ext he)
  have hr := d.stage.selectedFits
  have hf := d.stage.positiveWidth
  have hs := (selected_inside_slot d.stage slot axis).2
  unfold slotWidth at hs
  by_cases ho : slot.val<d.stage.target.val
  · right
    have hl := lower_slot d.stage slot d.stage.target ho
    have hn : (d.stage.f-1)*s.chunk+s.chunk=d.stage.f*s.chunk := by
      calc
        _ = (d.stage.f-1+1)*s.chunk := by ring
        _ = _ := by rw [Nat.sub_add_cancel hf]
    change slotLow d.stage d.stage.target+d.stage.rho+(d.stage.f-1)*s.chunk+1≤_
    omega
  · left
    have hl := lower_slot d.stage d.stage.target slot (by omega)
    change _<slotLow d.stage d.stage.target+d.stage.rho
    omega

theorem target (d : Inputs s) (i : Address d) (axis : Fin d.stage.f) :
    coordinates d (destination d i) axis d.stage.target=
      xor (coordinates d i axis d.stage.target) (coordinates d i axis d.stage.source) := by
  unfold coordinates
  have he := target_selected_position d.stage axis.val
  change (geometry d).after+axis.val*s.chunk=_ at he
  rw [←he,destination_bit,mask_selected,source_bit]

theorem other (d : Inputs s) (i : Address d) (axis : Fin d.stage.f) (slot : Fin d.stage.slots)
    (h : slot≠d.stage.target) : coordinates d (destination d i) axis slot=coordinates d i axis slot := by
  unfold coordinates
  rw [destination_bit]
  rcases other_position d slot axis h with hl | hh
  · rw [mask_below _ _ _ hl,Bool.xor_false]
  · rw [mask_above _ _ _ hh,Bool.xor_false]

/-- No coordinate-action hypothesis is supplied: the physical destination
itself implements the literal XOR operation on the complete original word. -/
theorem execute (d : Inputs s) (i : Address d) :
    coordinates d (destination d i)=Networks.BinaryRowColumns.execute (op d) (coordinates d i) := by
  funext axis slot
  by_cases h : slot=d.stage.target
  · subst slot
    simpa only [Networks.BinaryRowColumns.execute,op,Function.update_self] using target d i axis
  · simpa only [Networks.BinaryRowColumns.execute,op,Function.update_of_ne h] using other d i axis slot h

theorem other_bit_position (d : Inputs s) (slot : Fin d.stage.slots) (j : ℕ)
    (hj : j<slotWidth d.stage) (h : slot≠d.stage.target) :
    slotLow d.stage slot+j<(geometry d).after ∨
    (geometry d).after+(geometry d).n*(geometry d).q+1≤slotLow d.stage slot+j := by
  have hd : slot.val≠d.stage.target.val := fun he => h (Fin.ext he)
  have hr := d.stage.selectedFits
  have hf := d.stage.positiveWidth
  unfold slotWidth at hj
  by_cases ho : slot.val<d.stage.target.val
  · right
    have hl := lower_slot d.stage slot d.stage.target ho
    have hn : (d.stage.f-1)*s.chunk+s.chunk=d.stage.f*s.chunk := by
      calc
        _ = (d.stage.f-1+1)*s.chunk := by ring
        _ = _ := by rw [Nat.sub_add_cancel hf]
    change slotLow d.stage d.stage.target+d.stage.rho+(d.stage.f-1)*s.chunk+1≤_
    omega
  · left
    have hl := lower_slot d.stage d.stage.target slot (by omega)
    change _<slotLow d.stage d.stage.target+d.stage.rho
    omega

theorem other_slot_bit (d : Inputs s) (i : Address d) (slot : Fin d.stage.slots) (j : ℕ)
    (hj : j<slotWidth d.stage) (h : slot≠d.stage.target) :
    (word d (destination d i)).getD (slotLow d.stage slot+j) false=
      (word d i).getD (slotLow d.stage slot+j) false := by
  rw [destination_bit]
  rcases other_bit_position d slot j hj h with hl | hh
  · rw [mask_below _ _ _ hl,Bool.xor_false]
  · rw [mask_above _ _ _ hh,Bool.xor_false]

/-- Every bit of every other original slot is preserved, including columns
which the stage never selects. -/
theorem other_slot (d : Inputs s) (i : Address d) (slot : Fin d.stage.slots) (h : slot≠d.stage.target) :
    Gather.field (word d (destination d i)) (slotLow d.stage slot) (slotWidth d.stage)=
      Gather.field (word d i) (slotLow d.stage slot) (slotWidth d.stage) := by
  unfold Gather.field
  apply List.map_congr_left
  intro j hj
  exact other_slot_bit d i slot j (List.mem_range.mp hj) h

end
end IntegerMultBounds.Machine.ActivePrefixStageRuntimeCoordinates
