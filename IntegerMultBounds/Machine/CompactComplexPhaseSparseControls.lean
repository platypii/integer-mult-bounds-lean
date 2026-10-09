import IntegerMultBounds.Machine.CompactComplexPhaseControlCodec
import IntegerMultBounds.Machine.SparseSourceBitsRun
import IntegerMultBounds.Machine.BinaryAddressTable

/-! Literal sparse controls extracted from the complete runtime destination
address word. Low-first address scanning reverses the residual slot order;
the weight reversal is explicit. -/
namespace IntegerMultBounds.Machine.CompactComplexPhaseSparseControls
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageRuntimeOrdinal
open Networks Networks.ComplexPhaseRowSchedule
variable {s : Shape}

def stride (input : Inputs s) := input.stage.f*s.chunk
def residualSlot (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (i : Fin (dimension edge)) : Fin input.stage.slots := finCongr hslots.symm (slot edge i)
def reversedIndex (edge : Edge) (i : Fin (dimension edge)) : Fin (dimension edge) :=
  ⟨dimension edge-i.val-1,by have := i.isLt; omega⟩
def start (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (axis : Fin input.stage.f) (hdim : 0<dimension edge) :=
  originalPosition input.stage (residualSlot input hslots edge ⟨dimension edge-1,by omega⟩) axis
def address (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) := BinaryAddressTableData.row (s.active*s.chunk)
      (activeOrdinal s (CompactComplexPhasePhysical.destination input hslots edge k))

theorem dimension_le (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge) :
    dimension edge ≤ input.stage.slots := by
  by_cases h : 0<dimension edge
  · have hs := (residualSlot input hslots edge ⟨dimension edge-1,by omega⟩).isLt
    change dimension edge-1 < input.stage.slots at hs
    omega
  · omega

theorem position_lt (input : Inputs s) (sl : Fin input.stage.slots) (axis : Fin input.stage.f) :
    originalPosition input.stage sl axis<s.active*s.chunk := by
  have hs := ActivePrefixStageParameters.axes_split input.stage sl
  have hr := input.stage.selectedFits
  have ha := axis.isLt
  have he : ActivePrefixStageParameters.highAxes input.stage sl+axis.val+1≤s.active := by omega
  change input.stage.left+sl.val*input.stage.f+axis.val+1≤s.active at he
  have hd : s.active-(input.stage.left+sl.val*input.stage.f+axis.val)-1<s.active := by omega
  unfold originalPosition originalAxis
  nlinarith

theorem positions (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (axis : Fin input.stage.f) (hdim : 0<dimension edge) (i : Fin (dimension edge)) :
    start input hslots edge axis hdim+i.val*stride input=
      originalPosition input.stage (residualSlot input hslots edge (reversedIndex edge i)) axis := by
  have hd := dimension_le input hslots edge
  have hi := i.isLt
  rw [start,original_position,original_position]
  simp only [residualSlot,finCongr_apply,Fin.val_cast,slot_val,reversedIndex,
    ActivePrefixStageGeometry.slotLow,ActivePrefixStageParameters.lowAxes,stride]
  have h1 : input.stage.slots-(dimension edge-1)-1=input.stage.slots-dimension edge := by omega
  have h2 : input.stage.slots-(dimension edge-i.val-1)-1=input.stage.slots-dimension edge+i.val := by omega
  rw [h1,h2]
  ring

theorem span (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (axis : Fin input.stage.f) (hdim : 0<dimension edge) :
    start input hslots edge axis hdim+(dimension edge-1)*stride input<s.active*s.chunk := by
  have h := positions input hslots edge axis hdim ⟨dimension edge-1,by omega⟩
  rw [h]
  exact position_lt input _ axis

theorem address_value (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) : Counter.value (address input hslots edge k)=
      activeOrdinal s (CompactComplexPhasePhysical.destination input hslots edge k) := by
  apply BinaryAddressTableData.row_rank
  exact Nat.mod_lt _ (by positivity)

theorem extracted (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (hdim : 0<dimension edge) :
    SelectedSourceBitsData.selected (address input hslots edge k) (stride input)
      (start input hslots edge axis hdim) (dimension edge)=
      (CompactComplexPhaseControlCodec.bits input hslots edge k axis).reverse := by
  apply List.ext_getElem (by simp [CompactComplexPhaseControlCodec.bits])
  intro j hj hk
  have hj' : j<dimension edge := by simpa using hj
  rw [SelectedSourceBitsData.selected_entry _ _ _ _ _ hj',address_value]
  rw [positions input hslots edge axis hdim ⟨j,hj'⟩]
  simp only [CompactComplexPhaseControlCodec.bits,List.getElem_reverse,List.length_ofFn,List.getElem_ofFn,
    CompactComplexPhasePhysical.control,BinaryRowColumns.bit_scalar,highCoordinates,residualSlot,reversedIndex]
  congr 2
  apply Fin.ext
  simp only [finCongr_apply,Fin.val_cast,slot_val]
  omega

theorem materializes (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (hdim : 0<dimension edge)
    (hs : Fin 3 → List Bool)
    (hq : Counter.value (hs 0)=stride input)
    (hn : Counter.value (hs 1)=dimension edge-1)
    (hr : Counter.value (hs 2)=start input hslots edge axis hdim)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime (SparseSourceBitsRun.program (a := 2))
      (fun v => v=SparseSourceBitsRun.input (address input hslots edge k) hs)
      (fun v => v=SelectedSourceBitsBank.raw
        (SelectedSourceBitsCore.payload (SelectedSourceBitsScan.word (address input hslots edge k))
          (SelectedSourceBitsScan.word (CompactComplexPhaseControlCodec.bits input hslots edge k axis).reverse) 0 0) hs)
      (400*(s.active*s.chunk+1)) := by
  have hspan : start input hslots edge axis hdim+(dimension edge-1)*stride input<
      (address input hslots edge k).length := by
    simpa only [address,BinaryAddressTableData.row_length] using span input hslots edge axis hdim
  have hpos : 1≤stride input := Nat.mul_pos input.stage.positiveWidth (by have := input.stage.selectedFits; omega)
  have h := SparseSourceBitsRun.runs_linear (a := 2) (address input hslots edge k) hs
    (stride input) (start input hslots edge axis hdim) (dimension edge-1) hspan hpos hq hn hr hc
  have hn' : dimension edge-1+1=dimension edge := by omega
  change HoareTime _ _ (fun v => v=SelectedSourceBitsBank.raw
    (SelectedSourceBitsCore.payload (SelectedSourceBitsScan.word (address input hslots edge k))
      (SelectedSourceBitsScan.word (SelectedSourceBitsData.selected (address input hslots edge k)
        (stride input) (start input hslots edge axis hdim) (dimension edge-1+1))) 0 0) hs)
    (400*((address input hslots edge k).length+1)) at h
  rw [hn',extracted] at h
  simpa only [address,BinaryAddressTableData.row_length] using h

theorem address_width (input : Inputs s) : s.active*s.chunk+1≤s.payload := by
  have h := input.hrecord
  unfold Shape.bits at h
  omega

theorem extraction_charge (input : Inputs s) :
    400*(s.active*s.chunk+1)≤400*s.payload :=
  Nat.mul_le_mul_left _ (address_width input)

theorem address_table_charge (input : Inputs s) :
    BinaryAddressTable.constant*((s.active*s.chunk+1)*2^(s.active*s.chunk))≤
      BinaryAddressTable.constant*(2^(s.active*s.chunk)*s.payload) :=
  BinaryAddressTable.cost_volume _ _ (address_width input)

theorem weighted_reverse (ws : List (ZMod 4)) (bs : List Bool) (hl : ws.length=bs.length) :
    WeightedPhaseAccumulator.weightedSum ws.reverse bs.reverse=
      WeightedPhaseAccumulator.weightedSum ws bs := by
  unfold WeightedPhaseAccumulator.weightedSum
  rw [←List.reverse_zipWith hl,List.sum_reverse]

theorem extracted_readout (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (hdim : 0<dimension edge) :
    ((WeightedPhaseAccumulator.accumulate 0 (CompactComplexPhaseControlCodec.weights edge).reverse
      (SelectedSourceBitsData.selected (address input hslots edge k) (stride input)
        (start input hslots edge axis hdim) (dimension edge))).val : ZMod 4)=
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (target edge) (target_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis))-
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (source edge) (source_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis)) := by
  rw [extracted]
  have hl := CompactComplexPhaseControlCodec.lengths input hslots edge k axis
  rw [WeightedPhaseAccumulator.accumulate_cast _ _ _ (by simpa using hl),weighted_reverse _ _ hl.symm]
  rw [←WeightedPhaseAccumulator.accumulate_cast _ _ _ hl]
  exact CompactComplexPhaseControlCodec.readout input hslots edge k axis

end
end IntegerMultBounds.Machine.CompactComplexPhaseSparseControls
