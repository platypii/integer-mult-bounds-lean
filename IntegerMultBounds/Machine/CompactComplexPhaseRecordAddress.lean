import IntegerMultBounds.Machine.CompactActualSparseUnitPhase
import IntegerMultBounds.Machine.BinaryCurrentAddress

/-! Sparse phase controls are fields of the live complete record address.
The counter may wrap across global rows; its literal fixed-width word still
contains exactly the active coordinates used by the compiled phase. -/
namespace IntegerMultBounds.Machine.CompactComplexPhaseRecordAddress
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open CompactComplexPhaseSparseControls (stride start)
open Networks Networks.ComplexPhaseRowSchedule
variable {s : Shape}

def rank (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) :=
  (CompactComplexPhasePhysical.destination input hslots edge k).val/s.payload
def address (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) := BinaryAddressTableData.row s.bits (rank input hslots edge k)
def start (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (axis : Fin input.stage.f) (hdim : 0<dimension edge) :=
  s.H+s.B+CompactComplexPhaseSparseControls.start input hslots edge axis hdim

theorem active_fits : s.H+s.B+s.active*s.chunk≤s.bits := by
  unfold Shape.bits
  omega

theorem span (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (axis : Fin input.stage.f) (hdim : 0<dimension edge) :
    start input hslots edge axis hdim+(dimension edge-1)*stride input<s.bits := by
  have hs := CompactComplexPhaseSparseControls.span input hslots edge axis hdim
  have hf := active_fits (s := s)
  unfold start
  omega

theorem extracted (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (hdim : 0<dimension edge) :
    SelectedSourceBitsData.selected (address input hslots edge k) (stride input)
      (start input hslots edge axis hdim) (dimension edge)=
      (CompactComplexPhaseControlCodec.bits input hslots edge k axis).reverse := by
  rw [←CompactComplexPhaseSparseControls.extracted input hslots edge k axis hdim]
  apply List.ext_getElem (by simp)
  intro j hj hk
  have hj' : j<dimension edge := by simpa using hj
  have hs := CompactComplexPhaseSparseControls.span input hslots edge axis hdim
  have hmul := Nat.mul_le_mul_right (stride input) (by omega : j≤dimension edge-1)
  have hp : CompactComplexPhaseSparseControls.start input hslots edge axis hdim+j*stride input<s.active*s.chunk := by omega
  have hf : start input hslots edge axis hdim+j*stride input<s.bits := by
    have hb := active_fits (s := s)
    unfold start
    omega
  rw [SelectedSourceBitsData.selected_entry _ _ _ _ _ hj',
    SelectedSourceBitsData.selected_entry _ _ _ _ _ hj',
    CompactComplexPhaseSparseControls.address_value]
  simp only [address,BinaryAddressTableData.row_value,ActivePrefixStageRuntimeOrdinal.activeOrdinal,
    rank,Nat.testBit_mod_two_pow,hf,hp,decide_true,Bool.true_and,Nat.testBit_div_two_pow]
  unfold start
  congr 1
  omega

theorem readout (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (hdim : 0<dimension edge) :
    ((WeightedPhaseAccumulator.accumulate 0 (CompactComplexPhaseControlCodec.weights edge).reverse
      (SelectedSourceBitsData.selected (address input hslots edge k) (stride input)
        (start input hslots edge axis hdim) (dimension edge))).val : ZMod 4)=
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (target edge) (target_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis))-
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (source edge) (source_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis)) := by
  rw [extracted,←CompactComplexPhaseSparseControls.extracted input hslots edge k axis hdim]
  exact CompactComplexPhaseSparseControls.extracted_readout input hslots edge k axis hdim

theorem counter_matches (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) :
    address input hslots edge k=BinaryAddressTableData.row s.bits (rank input hslots edge k) := rfl

end
end IntegerMultBounds.Machine.CompactComplexPhaseRecordAddress
