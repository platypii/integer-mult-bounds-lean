import IntegerMultBounds.Machine.CompactLiteralUnitPhase

/-! Zero residual dimension has identically zero ordered phase and is compiled
as a tape-preserving halted program. It requires no fabricated sparse offset,
control record, or coefficient output stream. -/
namespace IntegerMultBounds.Machine.CompactZeroUnitPhase
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open Networks Networks.ComplexPhaseRowSchedule
variable {s : Shape}

theorem diagonal (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (hdim : dimension edge=0) :
    CompactComplexPhasePhysical.diagonal input hslots edge k axis=0 := by
  unfold CompactComplexPhasePhysical.diagonal
  have hempty : IsEmpty (Fin (dimension edge)) := by rw [hdim]; infer_instance
  let := hempty
  simp

theorem ordered_phase (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (hdim : dimension edge=0) :
    BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
      (target edge) (target_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis))-
    BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
      (source edge) (source_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis))=0 := by
  rw [CompactComplexPhasePhysical.original_phase,diagonal input hslots edge k axis hdim]
  split_ifs <;> simp

theorem coefficient_identity (input : Inputs s) (hslots : input.stage.slots=25^3) (edge : Edge)
    (k : Fin (input.rows*s.recordWidth)) (axis : Fin input.stage.f) (hdim : dimension edge=0) (z : ℂ) :
    BinaryPhase.phase
      (BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (target edge) (target_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis))-
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (source edge) (source_nondegenerate edge) (CompactComplexPhasePhysical.originalCoordinates input hslots k axis)))*z=z := by
  rw [ordered_phase input hslots edge k axis hdim,BinaryPhase.phase_zero,one_mul]

def program (t a : ℕ) (ht : 0<t) := skip t a ht

theorem runs {t a : ℕ} (ht : 0<t) (v : Tapes t a) :
    HoareTime (program t a ht) (fun z => z=v) (fun z => z=v) 0 := skip_hoare ht v

end
end IntegerMultBounds.Machine.CompactZeroUnitPhase
