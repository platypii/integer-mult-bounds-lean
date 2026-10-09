import IntegerMultBounds.Machine.UnitPhaseFullStreamArray
import IntegerMultBounds.Machine.CompactComplexPhaseRecordAddress

/-! The physical stream kernel's derived sparse offset and live full-address
readout yield the actual ordered complex25 phase. No phase exponent, controls
or supplied numeric sparse descriptors enter this semantic connection. -/
namespace IntegerMultBounds.Machine.CompactLiteralUnitPhase
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open Networks Networks.ComplexPhaseRowSchedule
variable {s : Shape}

theorem offset (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (axis : Fin input.stage.f) (hdim : 0<dimension edge) :
    SparsePhaseHeadersData.offset input.stage axis (dimension edge)=
      CompactComplexPhaseRecordAddress.start input hslots edge axis hdim := by
  simp [SparsePhaseHeadersData.offset,CompactComplexPhaseRecordAddress.start,
    CompactComplexPhaseSparseControls.start,CompactComplexPhaseSparseControls.residualSlot,
    ActivePrefixStageRuntimeOrdinal.originalPosition,ActivePrefixStageRuntimeOrdinal.originalAxis,
    slot_val,Nat.add_assoc]

theorem exponent (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (hdim : 0<dimension edge) :
    ((UnitPhaseRecordKernel.exponent input.stage axis (dimension edge)
      (CompactComplexPhaseControlCodec.weights edge).reverse
      (CompactComplexPhaseRecordAddress.address input hslots edge k)).val : ZMod 4)=
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (target edge) (target_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis))-
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (source edge) (source_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis)) := by
  have hm : dimension edge-1+1=dimension edge := by omega
  simpa only [UnitPhaseRecordKernel.exponent,UnitPhaseRecordKernel.selected,SparseWeightedUnitPhase.selected,
    hm,offset input hslots edge axis hdim,CompactComplexPhaseSparseControls.stride] using
      CompactComplexPhaseRecordAddress.readout input hslots edge k axis hdim

theorem span (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (axis : Fin input.stage.f) (hdim : 0<dimension edge) :
    SparsePhaseHeadersData.offset input.stage axis (dimension edge)+
      (dimension edge-1)*(input.stage.f*s.chunk)<s.bits := by
  rw [offset input hslots edge axis hdim]
  exact CompactComplexPhaseRecordAddress.span input hslots edge axis hdim

theorem coefficient_phase (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (hdim : 0<dimension edge)
    (a : ButterflyStreamData.Coefficient) (b n : ℕ)
    (hw : a.1.length=b+1 ∧ a.2.length=b+1)
    (hg : ∀ j : Fin 2,|ButterflySigned.signedValue b (UnitPhaseStreamEndpoint.components a j.val)|<(2^b : ℕ)) :
    let p := UnitPhaseRecordKernel.exponent input.stage axis (dimension edge)
      (CompactComplexPhaseControlCodec.weights edge).reverse (CompactComplexPhaseRecordAddress.address input hslots edge k)
    ButterflySigned.complexValue
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 0 (UnitPhaseStreamEndpoint.components a)))
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 1 (UnitPhaseStreamEndpoint.components a))) n=
      BinaryPhase.phase
        (BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
          (target edge) (target_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis))-
        BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
          (source edge) (source_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis)))*
        ButterflySigned.complexValue (ButterflySigned.signedValue b a.1) (ButterflySigned.signedValue b a.2) n := by
  have hc : ∀ j,(UnitPhaseStreamEndpoint.components a j).length=b+1 := by
    intro j
    unfold UnitPhaseStreamEndpoint.components
    split_ifs <;> first | exact hw.1 | exact hw.2
  have h := UnitPhaseSigned.words_phase
    (UnitPhaseRecordKernel.exponent input.stage axis (dimension edge)
      (CompactComplexPhaseControlCodec.weights edge).reverse (CompactComplexPhaseRecordAddress.address input hslots edge k))
    (UnitPhaseStreamEndpoint.components a) b n hc hg
  rw [exponent input hslots edge k axis hdim] at h
  exact h

end
end IntegerMultBounds.Machine.CompactLiteralUnitPhase
