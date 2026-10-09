import IntegerMultBounds.Machine.ActivePrefixStageRuntimeSelected
import IntegerMultBounds.Machine.ActivePrefixSelectedOffsetData

/-! Literal complete active words and bits of the physically selected stage.
The source control and target mask are extracted from original addresses. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeWord
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (geometry Address)
open ActivePrefixStageRuntimeSelected
open ActivePrefixStageParameters ActivePrefixStageGeometry
open BinaryAddressTableData (row row_length)
variable {s : Shape}

def word (d : Inputs s) (i : Address d) : List Bool :=
  row (geometry d).after i.activeAfter.val++row ((geometry d).n*(geometry d).q) i.target.val++
    row (geometry d).before i.activeBefore.val

def mask (d : Inputs s) (i : Address d) : List Bool :=
  List.replicate (geometry d).after false++Compact.PowerTwo.toggleMask s.chunk (lowControl d i)++
    (highControl d i::List.replicate ((geometry d).before-1) false)

theorem word_length (d : Inputs s) (i : Address d) : (word d i).length=s.active*s.chunk := by
  simp only [word,List.length_append,row_length]
  have h := (geometry d).activeSize
  omega

theorem destination_word (d : Inputs s) (i : Address d) :
    word d (destination d i)=List.zipWith xor (word d i) (mask d i) := by
  have hf := fields d i
  have ha : (destination d i).activeAfter=i.activeAfter := by rw [hf]
  have h := target_word d i (row (geometry d).after i.activeAfter.val)
  simpa only [word,mask,ActiveTargetHighestLayoutCompose.targetWord,row_length,ha] using h

theorem zip_bit (xs ys : List Bool) (j : ℕ) (hl : xs.length=ys.length) :
    (List.zipWith xor xs ys).getD j false=xor (xs.getD j false) (ys.getD j false) := by
  induction xs generalizing ys j with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      cases j with
      | zero => rfl
      | succ j =>
        change (List.zipWith xor xs ys).getD j false=xor (xs.getD j false) (ys.getD j false)
        exact ih ys j (by simpa using hl)

theorem toggle_bit (q : ℕ) (hq : 1≤q) (zs : List Bool) (j : ℕ) (hj : j<zs.length) :
    (Compact.PowerTwo.toggleMask q zs).getD (j*q) false=zs.getD j false := by
  induction zs generalizing j with
  | nil => simp at hj
  | cons z zs ih =>
    rw [Compact.PowerTwo.toggleMask_cons]
    cases j with
    | zero => simp
    | succ j =>
      have hl : (z::List.replicate (q-1) false).length=q := by simp; omega
      rw [List.getD_append_right _ _ _ _ (by rw [hl,Nat.add_mul,Nat.one_mul]; omega),hl]
      have he : (j+1)*q-q=j*q := by rw [Nat.add_mul,Nat.one_mul,Nat.add_sub_cancel]
      rw [he,ih j (by simpa using hj)]
      rfl

theorem low_length (d : Inputs s) (i : Address d) : (lowControl d i).length=d.stage.f-1 := by
  unfold lowControl ActiveRepairLayoutPermutationFiber.controlWord
  split_ifs <;> simp [geometry,parameters]

theorem mask_length (d : Inputs s) (i : Address d) : (mask d i).length=s.active*s.chunk := by
  have hq : 1≤s.chunk := by have := d.stage.selectedFits; omega
  have hb := positive_before d.stage
  have hs := (geometry d).activeSize
  simp only [mask,List.length_append,List.length_replicate,List.length_cons,
    Compact.PowerTwo.toggleMask_length s.chunk hq,low_length]
  change (geometry d).after+(geometry d).n*(geometry d).q+(((geometry d).before-1)+1)=_
  change 1≤(geometry d).before at hb
  omega

theorem destination_bit (d : Inputs s) (i : Address d) (j : ℕ) :
    (word d (destination d i)).getD j false=xor ((word d i).getD j false) ((mask d i).getD j false) := by
  rw [destination_word,zip_bit _ _ _ (by rw [word_length,mask_length])]

theorem selected_bit (d : Inputs s) (i : Address d) (axis : Fin d.stage.f) :
    (lowControl d i++[highControl d i]).getD axis.val false=
      (source d i).getD (d.stage.rho+axis.val*s.chunk) false := by
  rw [←selected]
  simp only [SelectedSourceBitsData.selected,List.getD_eq_getElem?_getD,
    List.getElem?_map,List.getElem?_range axis.isLt,Option.map_some,Option.getD_some]

theorem mask_selected (d : Inputs s) (i : Address d) (axis : Fin d.stage.f) :
    (mask d i).getD ((geometry d).after+axis.val*s.chunk) false=
      (source d i).getD (d.stage.rho+axis.val*s.chunk) false := by
  have hq : 1≤s.chunk := by have := d.stage.selectedFits; omega
  have hf := d.stage.positiveWidth
  have hl := low_length d i
  have hm := Compact.PowerTwo.toggleMask_length s.chunk hq (lowControl d i)
  have hb := positive_before d.stage
  rw [mask,List.append_assoc,List.getD_append_right _ _ _ _ (by simp),List.length_replicate,Nat.add_sub_cancel_left]
  rw [←selected_bit]
  by_cases h : axis.val<d.stage.f-1
  · rw [List.getD_append _ _ _ _ (by rw [hm,hl]; exact Nat.mul_lt_mul_of_pos_right h hq),
      toggle_bit s.chunk hq _ axis.val (by rwa [hl]),List.getD_append _ _ _ _ (by rwa [hl])]
  · have he : axis.val=d.stage.f-1 := by have := axis.isLt; omega
    rw [List.getD_append_right _ _ _ _ (by rw [hm,hl,he]),hm,hl,he,Nat.sub_self]
    rw [List.getD_append_right _ _ _ _ (by rw [hl]),hl,Nat.sub_self]
    simp

theorem before_bit (d : Inputs s) (i : Address d) (j : ℕ) :
    (word d i).getD ((geometry d).after+(geometry d).n*(geometry d).q+j) false=
      (row (geometry d).before i.activeBefore.val).getD j false := by
  rw [word,List.getD_append_right _ _ _ _ (by simp only [List.length_append,row_length]; omega)]
  simp only [List.length_append,row_length,Nat.add_sub_cancel_left]

theorem after_bit (d : Inputs s) (i : Address d) (j : ℕ) (hj : j<(geometry d).after) :
    (word d i).getD j false=(row (geometry d).after i.activeAfter.val).getD j false := by
  rw [word,List.append_assoc,List.getD_append _ _ _ _ (by simpa only [row_length] using hj)]

theorem source_bit (d : Inputs s) (i : Address d) (axis : Fin d.stage.f) :
    (source d i).getD (d.stage.rho+axis.val*s.chunk) false=
      (word d i).getD (slotLow d.stage d.stage.source+(d.stage.rho+axis.val*s.chunk)) false := by
  have hi : d.stage.rho+axis.val*s.chunk<d.stage.f*s.chunk := by
    have hm := Nat.mul_le_mul_right s.chunk (show axis.val+1≤d.stage.f by have := axis.isLt; omega)
    rw [Nat.add_mul,Nat.one_mul] at hm
    have := d.stage.selectedFits
    omega
  by_cases ho : d.stage.source.val<d.stage.target.val
  · rw [source,ite_eq_left ho,ActiveRepairLayoutPermutationFiber.sourceWord]
    change (Gather.field (row (geometry d).before i.activeBefore.val) (earlyOffset d.stage)
      (d.stage.f*s.chunk)).getD (d.stage.rho+axis.val*s.chunk) false=_
    rw [ActivePrefixSelectedOffsetData.field_bit _ _ _ _ hi]
    have he := early_source_selected_position d.stage ho axis.val
    change (geometry d).after+(geometry d).n*(geometry d).q+
      (earlyOffset d.stage+d.stage.rho+axis.val*s.chunk)=_ at he
    rw [←he,before_bit]
    congr 1
    omega
  · have hl := late_fits d.stage (ActivePrefixStageOrderCompare.late_of_not_early d.stage ho)
    rw [source,ite_eq_right ho,ActiveRepairLayoutPermutationFiber.sourceWord]
    change (Gather.field (row (geometry d).after i.activeAfter.val) (lateOffset d.stage)
      (d.stage.f*s.chunk)).getD (d.stage.rho+axis.val*s.chunk) false=_
    rw [ActivePrefixSelectedOffsetData.field_bit _ _ _ _ hi]
    have he := late_source_selected_position d.stage axis.val
    rw [←he,after_bit _ _ _ (by change _<after d.stage; omega)]
    congr 1
    omega

theorem zeros_bit (n j : ℕ) : (List.replicate n false).getD j false=false := by
  by_cases h : j<n
  · exact List.getD_replicate false h
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem mask_below (d : Inputs s) (i : Address d) (j : ℕ) (hj : j<(geometry d).after) :
    (mask d i).getD j false=false := by
  rw [mask,List.append_assoc,List.getD_append _ _ _ _ (by simpa using hj),zeros_bit]

theorem mask_above (d : Inputs s) (i : Address d) (j : ℕ)
    (hj : (geometry d).after+(geometry d).n*(geometry d).q+1≤j) :
    (mask d i).getD j false=false := by
  have hq : 1≤s.chunk := by have := d.stage.selectedFits; omega
  have hm : (Compact.PowerTwo.toggleMask s.chunk (lowControl d i)).length=(geometry d).n*(geometry d).q := by
    rw [Compact.PowerTwo.toggleMask_length s.chunk hq,low_length]
    rfl
  rw [mask,List.getD_append_right _ _ _ _ (by simp only [List.length_append,List.length_replicate,hm]; omega)]
  simp only [List.length_append,List.length_replicate,hm]
  have he : j-((geometry d).after+(geometry d).n*(geometry d).q)=
      (j-((geometry d).after+(geometry d).n*(geometry d).q)-1)+1 := by omega
  rw [he,List.getD_cons_succ,zeros_bit]

end
end IntegerMultBounds.Machine.ActivePrefixStageRuntimeWord
