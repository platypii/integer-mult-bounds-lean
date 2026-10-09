import IntegerMultBounds.Machine.CompactComplexPhaseRecordAddress

/-! All residual-slot and coordinate-axis controls occupy one sparse chunk
stream. Low-first scanning reverses both slots and axes; each static residual
weight therefore applies to an adjacent runtime-width block. -/
namespace IntegerMultBounds.Machine.CompactAllAxisPhaseControls
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageRuntimeOrdinal
open CompactComplexPhaseSparseControls (residualSlot reversedIndex)
open Networks Networks.ComplexPhaseRowSchedule
variable {s : Shape}

def start (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (hm : 0<dimension edge) :=
  s.H+s.B+ActivePrefixStageGeometry.slotLow input.stage
    (residualSlot input hslots edge ⟨dimension edge-1,by omega⟩)+input.stage.rho

theorem positions (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (hm : 0<dimension edge) (i : Fin (dimension edge)) (j : Fin input.stage.f) :
    start input hslots edge hm+(i.val*input.stage.f+j.val)*s.chunk=
      s.H+s.B+originalPosition input.stage
        (residualSlot input hslots edge (reversedIndex edge i)) (reverseAxis j) := by
  rw [original_position]
  have hd := CompactComplexPhaseSparseControls.dimension_le input hslots edge
  have hi := i.isLt
  have hj := j.isLt
  simp only [start,residualSlot,finCongr_apply,Fin.val_cast,slot_val,reversedIndex,
    ActivePrefixStageGeometry.slotLow,ActivePrefixStageParameters.lowAxes,reverseAxis]
  have h1 : input.stage.slots-(dimension edge-1)-1=input.stage.slots-dimension edge := by omega
  have h2 : input.stage.slots-(dimension edge-i.val-1)-1=input.stage.slots-dimension edge+i.val := by omega
  have h3 : input.stage.f-(input.stage.f-j.val-1)-1=j.val := by omega
  rw [h1,h2,h3]
  ring

/-- The complete all-axis sparse stream fits in the full physical address. -/
theorem span (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (hm : 0<dimension edge) :
    start input hslots edge hm+(dimension edge*input.stage.f-1)*s.chunk<s.bits := by
  have hf := input.stage.positiveWidth
  let i : Fin (dimension edge) := ⟨dimension edge-1,by omega⟩
  let j : Fin input.stage.f := ⟨input.stage.f-1,by omega⟩
  have hp := positions input hslots edge hm i j
  have he : i.val*input.stage.f+j.val=dimension edge*input.stage.f-1 := by
    dsimp [i,j]
    have h : dimension edge-1+1=dimension edge := by omega
    have hh := congrArg (fun n => n*input.stage.f) h
    simp only [Nat.add_mul,Nat.one_mul] at hh
    omega
  rw [he] at hp
  rw [hp]
  have hs := CompactComplexPhaseSparseControls.position_lt input
    (residualSlot input hslots edge (reversedIndex edge i)) (reverseAxis j)
  have hb := CompactComplexPhaseRecordAddress.active_fits (s := s)
  omega

/-- A block contains all axes of one reversed residual slot. -/
theorem extracted_entry (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (hm : 0<dimension edge)
    (i : Fin (dimension edge)) (j : Fin input.stage.f) :
    (SelectedSourceBitsData.selected
      (CompactComplexPhaseRecordAddress.address input hslots edge k) s.chunk
      (start input hslots edge hm) (dimension edge*input.stage.f))[i.val*input.stage.f+j.val]'(by
        simp only [SelectedSourceBitsData.selected_length]
        have hi := i.isLt
        have hj := j.isLt
        nlinarith)=
      (CompactComplexPhaseControlCodec.bits input hslots edge k (reverseAxis j))[dimension edge-i.val-1]'(by
        simp only [CompactComplexPhaseControlCodec.bits,List.length_ofFn]
        have hi := i.isLt
        omega) := by
  have hindex : i.val*input.stage.f+j.val<dimension edge*input.stage.f := by
    have hi := i.isLt
    have hj := j.isLt
    nlinarith
  have hp : start input hslots edge hm+(i.val*input.stage.f+j.val)*s.chunk=
      CompactComplexPhaseRecordAddress.start input hslots edge (reverseAxis j) hm+
        i.val*CompactComplexPhaseSparseControls.stride input := by
    rw [positions]
    unfold CompactComplexPhaseRecordAddress.start
    rw [show s.H+s.B+CompactComplexPhaseSparseControls.start input hslots edge (reverseAxis j) hm+
      i.val*CompactComplexPhaseSparseControls.stride input=
      s.H+s.B+(CompactComplexPhaseSparseControls.start input hslots edge (reverseAxis j) hm+
        i.val*CompactComplexPhaseSparseControls.stride input) by omega,
      CompactComplexPhaseSparseControls.positions]
  rw [SelectedSourceBitsData.selected_entry _ _ _ _ _ hindex,hp]
  have he := congrArg (fun bs : List Bool => bs.getD i.val false)
    (CompactComplexPhaseRecordAddress.extracted input hslots edge k (reverseAxis j) hm)
  have hl : i.val<(CompactComplexPhaseControlCodec.bits input hslots edge k (reverseAxis j)).reverse.length := by
    simp only [List.length_reverse,CompactComplexPhaseControlCodec.bits,List.length_ofFn]
    exact i.isLt
  rw [List.getD_eq_getElem _ _ (by simp),
    SelectedSourceBitsData.selected_entry _ _ _ _ _ i.isLt,
    List.getD_eq_getElem _ _ hl,List.getElem_reverse] at he
  have hidx : dimension edge-1-i.val=dimension edge-i.val-1 := by omega
  simpa only [CompactComplexPhaseControlCodec.bits,List.length_ofFn,hidx] using he

end
end IntegerMultBounds.Machine.CompactAllAxisPhaseControls
