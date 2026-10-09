import IntegerMultBounds.Machine.ActiveRepairEarlyFieldsPlaced
import IntegerMultBounds.Machine.CountedRepairKeyValue

/-! The actual extracted-field computation has the existing exact local guard
and repair-destination rank semantics. A concatenated word is used only in
this mathematical identification, never as a supplied physical machine input. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyFieldsValue
noncomputable section
open IntegerMultBounds.Compact
open IntegerMultBounds.Compact.PowerTwo

private theorem low_field (V W : List Bool) : Gather.field (V++W) 0 V.length=V := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [Gather.field,List.getElem_map,List.getElem_range,zero_add]
    rw [List.getD_append V W false j hj']
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some]

private theorem high_field (V W : List Bool) : Gather.field (V++W) V.length W.length=W := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [Gather.field,List.getElem_map,List.getElem_range]
    rw [List.getD_append_right V W false (V.length+j) (by omega)]
    simp only [Nat.add_sub_cancel_left,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj',Option.getD_some]

theorem original_fields (q b : ℕ) (V W Z : List Bool)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b) :
    CountedRepairKeyBank.V q Z (V++W)=V ∧ CountedRepairKeyBank.W q b Z (V++W)=W := by
  constructor
  · simpa only [CountedRepairKeyBank.V,hV] using low_field V W
  · simpa only [CountedRepairKeyBank.W,hV,hW] using high_field V W

theorem local_bound (q b : ℕ) (hq : 1≤q) (V W Z : List Bool)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b) :
    Counter.value (V++W)<Mi q b Z := by
  rw [Mi_eq q b Z hq,←pow_add]
  have h := Counter.value_lt (V++W)
  simpa only [List.length_append,hV,hW,Nat.add_comm] using h

theorem flag_rank (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q) (V W Z : List Bool)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b) :
    ActiveRepairEarlyFieldsBank.flag q b V W Z=
      rankFlag (rankEquiv q b Z) (badSet q b Z) (Counter.value (V++W)) := by
  have h := CountedRepairKeyValue.flag_rank q b hb hbq Z (V++W) _
    (local_bound q b (by omega) V W Z hV hW) rfl
  obtain ⟨hv,hw⟩ := original_fields q b V W Z hV hW
  rw [hv,hw] at h
  exact h

theorem destination_bits (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W Z : List Bool)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b) :
    CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z ++ PackedInverse.w q b hb hbq V W Z=
      rankKey (rankEquiv q b Z) (Sperm q b Z) (Tperm q b Z)
        (Z.length*q+Z.length*b) (Counter.value (V++W)) := by
  have h := CountedRepairKeyValue.bits_rank q b hb hbq Z (V++W) _
    (local_bound q b (by omega) V W Z hV hW) rfl
  obtain ⟨hv,hw⟩ := original_fields q b V W Z hV hW
  rw [hv,hw] at h
  exact h

end
end IntegerMultBounds.Machine.ActiveRepairEarlyFieldsValue
