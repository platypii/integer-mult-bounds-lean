import IntegerMultBounds.Machine.ActivePrefixStageNativePairCoordinates
import IntegerMultBounds.Machine.CompactLiteralUnitPhase
import IntegerMultBounds.Machine.UnitPhasePolynomialLiteralEndpoint

/-! Actual complex-network phase controls are read at the row ordinal reached
by the real native basis word. The original signed phase theorem therefore
applies to native coefficient streams without an assumed address interchange. -/
namespace IntegerMultBounds.Machine.CompactNativePhaseCoordinates
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageTripleWords (count)
open ActivePrefixStageNativePairCoordinates (start run)
open Networks Networks.ComplexPhaseRowSchedule
variable {s : Shape}

theorem rank_after_word (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (r : Fin (count d)) :
    CompactComplexPhaseRecordAddress.rank d hslots edge (start d r)=
      (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots edge) r).val := by
  unfold CompactComplexPhaseRecordAddress.rank CompactComplexPhasePhysical.destination
  rw [ActivePrefixStageNativePairCoordinates.run_start]
  change _*s.payload/s.payload=_
  exact Nat.mul_div_cancel _ (by have := d.hrecord; omega)

theorem address_after_word (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (r : Fin (count d)) :
    CompactComplexPhaseRecordAddress.address d hslots edge (start d r)=
      BinaryAddressTableData.row s.bits (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots edge) r).val := by
  unfold CompactComplexPhaseRecordAddress.address
  rw [rank_after_word]

/-- This is the actual phase of the polynomial stream's destination row,
with the original address expressed by the physically executed basis word. -/
theorem coefficient_phase (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (r : Fin (count d)) (axis : Fin d.stage.f) (hdim : 0<dimension edge)
    (a : ButterflyStreamData.Coefficient) (b n : ℕ)
    (hw : a.1.length=b+1 ∧ a.2.length=b+1)
    (hg : ∀ j : Fin 2,|ButterflySigned.signedValue b (UnitPhaseStreamEndpoint.components a j.val)|<(2^b : ℕ)) :
    let p := UnitPhasePolynomialLiteralEndpoint.phase d.stage axis (dimension edge)
      (CompactComplexPhaseControlCodec.weights edge).reverse
      (ActivePrefixStageNativePairCoordinates.run d (CompactComplexPhasePhysical.word d hslots edge) r).val
    ButterflySigned.complexValue
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 0 (UnitPhaseStreamEndpoint.components a)))
      (ButterflySigned.signedValue b (UnitPhaseNumerator.words p 1 (UnitPhaseStreamEndpoint.components a))) n=
      BinaryPhase.phase
        (BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
          (target edge) (target_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates d hslots (start d r) axis))-
        BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
          (source edge) (source_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates d hslots (start d r) axis)))*
        ButterflySigned.complexValue (ButterflySigned.signedValue b a.1) (ButterflySigned.signedValue b a.2) n := by
  have h := CompactLiteralUnitPhase.coefficient_phase d hslots edge (start d r) axis hdim a b n hw hg
  rw [address_after_word] at h
  exact h

end
end IntegerMultBounds.Machine.CompactNativePhaseCoordinates
