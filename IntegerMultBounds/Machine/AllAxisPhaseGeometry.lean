import IntegerMultBounds.Machine.AllAxisPhaseFlagsCaller
import IntegerMultBounds.Machine.CompactAllAxisPhaseReadout

/-! Physical all-axis header arithmetic starts at exactly the original tensor
control bit selected by the compact complex25 address compiler. -/
namespace IntegerMultBounds.Machine.AllAxisPhaseGeometry
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageFullData (Inputs)
open Networks Networks.ComplexPhaseRowSchedule
variable {s : Shape}

theorem offset_slot (v : Stage s) (m : ℕ) (hm : 0<m) (hslots : m≤v.slots) :
    AllAxisPhaseHeadersData.offset v m=s.H+s.B+
      ActivePrefixStageGeometry.slotLow v (⟨m-1,by omega⟩ : Fin v.slots)+v.rho := by
  have hs := v.activeAxes
  have hp := Nat.mul_le_mul_right v.f hslots
  have he := congrArg (fun n => n*v.f) (Nat.sub_add_cancel hslots)
  simp only [Nat.add_mul] at he
  have hsub : s.active-(v.left+m*v.f)=(v.slots-m)*v.f+v.right := by omega
  have hindex : v.slots-(m-1)-1=v.slots-m := by omega
  simp only [AllAxisPhaseHeadersData.offset,ActivePrefixStageGeometry.slotLow,
    lowAxes,hsub,hindex]

theorem offset_start (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (hm : 0<dimension edge) :
    AllAxisPhaseHeadersData.offset input.stage (dimension edge)=
      CompactAllAxisPhaseControls.start input hslots edge hm := by
  rw [offset_slot input.stage (dimension edge) hm
    (CompactComplexPhaseSparseControls.dimension_le input hslots edge)]
  rfl

theorem span (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (hm : 0<dimension edge) :
    AllAxisPhaseHeadersData.offset input.stage (dimension edge)+
      (dimension edge*input.stage.f-1)*s.chunk<s.bits := by
  rw [offset_start input hslots edge hm]
  exact CompactAllAxisPhaseControls.span input hslots edge hm

theorem controls_eq (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (hm : 0<dimension edge) :
    AllAxisPhaseFlagsCaller.controls input.stage (dimension edge)
      (CompactComplexPhaseRecordAddress.address input hslots edge k)=
      CompactAllAxisPhaseReadout.bits input hslots edge k hm := by
  unfold AllAxisPhaseFlagsCaller.controls CompactAllAxisPhaseReadout.bits
  rw [offset_start input hslots edge hm]

theorem phase_readout (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (hm : 0<dimension edge) :
    ((AllAxisPhaseFlagsCaller.phase input.stage (dimension edge)
      (CompactComplexPhaseControlCodec.weights edge).reverse
      (CompactComplexPhaseRecordAddress.address input hslots edge k)).val : ZMod 4)=
      ∑ axis : Fin input.stage.f,CompactAllAxisPhaseReadout.delta input hslots edge k axis := by
  unfold AllAxisPhaseFlagsCaller.phase
  rw [controls_eq input hslots edge k hm]
  exact CompactAllAxisPhaseReadout.accumulator_readout input hslots edge k hm

end
end IntegerMultBounds.Machine.AllAxisPhaseGeometry
