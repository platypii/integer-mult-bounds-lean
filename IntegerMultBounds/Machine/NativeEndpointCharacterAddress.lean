import IntegerMultBounds.Machine.AllAxisPhaseGeometry

/-! The endpoint character's single low-first address traversal reads every
original coordinate and runtime column, reversing both high-first indices
explicitly. This is derived from actual global serialized record ranks. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterAddress
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageRuntimeOrdinal (reverseAxis originalPosition highCoordinates)
variable {s : Shape}

def reverseSlot (v : Stage s) (i : Fin v.slots) : Fin v.slots :=
  ⟨v.slots-i.val-1,by have := i.isLt; omega⟩

theorem position (v : Stage s) (i : Fin v.slots) (j : Fin v.f) :
    AllAxisPhaseHeadersData.offset v v.slots+(i.val*v.f+j.val)*s.chunk=
      s.H+s.B+originalPosition v (reverseSlot v i) (reverseAxis j) := by
  have hi := i.isLt
  have hj := j.isLt
  have hs : 0<v.slots := by omega
  rw [AllAxisPhaseGeometry.offset_slot v v.slots hs le_rfl,
    ActivePrefixStageRuntimeOrdinal.original_position]
  have hlast : v.slots-(v.slots-1)-1=0 := by omega
  have hrev : v.slots-(v.slots-i.val-1)-1=i.val := by omega
  have hjrev : v.f-(v.f-j.val-1)-1=j.val := by omega
  simp only [ActivePrefixStageGeometry.slotLow,ActivePrefixStageParameters.lowAxes,
    reverseSlot,reverseAxis,hlast,hrev,hjrev,zero_mul,zero_add]
  ring

theorem position_lt (v : Stage s) (i : Fin v.slots) (j : Fin v.f) :
    originalPosition v i j<s.active*s.chunk := by
  have hs := ActivePrefixStageParameters.axes_split v i
  have hr := v.selectedFits
  have ha := j.isLt
  have he : ActivePrefixStageParameters.highAxes v i+j.val+1≤s.active := by omega
  change v.left+i.val*v.f+j.val+1≤s.active at he
  have hd : s.active-(v.left+i.val*v.f+j.val)-1<s.active := by omega
  unfold originalPosition ActivePrefixStageRuntimeOrdinal.originalAxis
  nlinarith

theorem span (v : Stage s) :
    AllAxisPhaseHeadersData.offset v v.slots+(v.slots*v.f-1)*s.chunk<s.bits := by
  have hs : 0<v.slots := by have := v.source.isLt; omega
  have hf := v.positiveWidth
  let i : Fin v.slots := ⟨v.slots-1,by omega⟩
  let j : Fin v.f := ⟨v.f-1,by omega⟩
  have he : i.val*v.f+j.val=v.slots*v.f-1 := by
    dsimp [i,j]
    have h1 : v.slots-1+1=v.slots := by omega
    have h2 : v.f-1+1=v.f := by omega
    have hmul := congrArg (fun n => n*v.f) h1
    simp only [Nat.add_mul,Nat.one_mul] at hmul
    omega
  rw [←he,position]
  have hp := position_lt v (reverseSlot v i) (reverseAxis j)
  unfold Shape.bits
  omega

theorem selected (v : Stage s) {rows : ℕ} (k : Fin (rows*s.recordWidth))
    (i : Fin v.slots) (j : Fin v.f) :
    (AllAxisPhaseFlagsCaller.controls v v.slots
      (BinaryAddressTableData.row s.bits (k.val/s.payload))).getD (i.val*v.f+j.val) false=
      highCoordinates v k (reverseAxis j) (reverseSlot v i) := by
  have hi := i.isLt
  have hj := j.isLt
  have hidx : i.val*v.f+j.val<v.slots*v.f := by nlinarith
  have hp := position_lt v (reverseSlot v i) (reverseAxis j)
  have hf : s.H+s.B+originalPosition v (reverseSlot v i) (reverseAxis j)<s.bits := by
    unfold Shape.bits
    omega
  unfold AllAxisPhaseFlagsCaller.controls
  rw [List.getD_eq_getElem _ _ (by simpa only [SelectedSourceBitsData.selected_length] using hidx),
    SelectedSourceBitsData.selected_entry _ _ _ _ _ hidx,position]
  simp only [BinaryAddressTableData.row_value,highCoordinates,
    ActivePrefixStageRuntimeOrdinal.activeOrdinal,Nat.testBit_mod_two_pow,hf,hp,
    decide_true,Bool.true_and,Nat.testBit_div_two_pow]
  congr 1
  omega

end
end IntegerMultBounds.Machine.NativeEndpointCharacterAddress
