import IntegerMultBounds.Machine.ActivePrefixStagePairCoordinates
import IntegerMultBounds.Machine.CompactComplexPhaseSchedule

/-! The actual complex25 phase compiler's literal row word is implemented by
physical compact stages. Controls are original-address bilinear coordinates;
ordered descending edges retain their negative phase. -/
namespace IntegerMultBounds.Machine.CompactComplexPhasePhysical
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageRuntimeOrdinal (highCoordinates)
open Networks
open Networks.ComplexPhaseRowSchedule
open ActiveRepairLayoutRecordsData (Array)
variable {s : Shape}

abbrev node (d : Inputs s) : CompactBinaryBasisSchedule.Node s where
  slots := d.stage.slots
  f := d.stage.f
  left := d.stage.left
  right := d.stage.right
  rho := d.stage.rho
  activeAxes := d.stage.activeAxes
  positiveWidth := d.stage.positiveWidth
  widthFits := d.stage.widthFits
  selectedFits := d.stage.selectedFits

def word (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge) : List (BinaryRowProgram.Op (Fin d.stage.slots)) :=
  CompactComplexPhaseSchedule.nodeWord (node d) hslots edge

def destination (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (k : Fin (d.rows*s.recordWidth)) := ActivePrefixStagePairCoordinates.run d (word d hslots edge) k

def originalCoordinates (d : Inputs s) (hslots : d.stage.slots=25^3)
    (k : Fin (d.rows*s.recordWidth)) (axis : Fin d.stage.f) : Fin (25^3) → ZMod 2 :=
  BinaryRowColumns.coordinates (highCoordinates d.stage k) axis ∘ finCongr hslots.symm

def control (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (k : Fin (d.rows*s.recordWidth)) (axis : Fin d.stage.f) (i : Fin (dimension edge)) : ZMod 2 :=
  BinaryRowColumns.scalar (highCoordinates d.stage (destination d hslots edge k) axis
    (finCongr hslots.symm (slot edge i)))

theorem coordinate_run (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (k : Fin (d.rows*s.recordWidth)) (axis : Fin d.stage.f) :
    BinaryRowColumns.coordinates (highCoordinates d.stage (destination d hslots edge k)) axis=
      Networks.BinaryRowProgram.run (Networks.ComplexPhaseRowSchedule.word edge)
        (originalCoordinates d hslots k axis) ∘ finCongr hslots := by
  rw [destination,ActivePrefixStagePairCoordinates.high_run_coordinates d (word d hslots edge) k,
    BinaryRowColumns.run_coordinates]
  have he : originalCoordinates d hslots k axis ∘ finCongr hslots=
      BinaryRowColumns.coordinates (highCoordinates d.stage k) axis := by
    funext j
    simp [originalCoordinates]
  rw [←he]
  exact CompactComplexPhaseSchedule.nodeWord_run (node d) hslots edge _

theorem computed_control (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (k : Fin (d.rows*s.recordWidth)) (axis : Fin d.stage.f) (i : Fin (dimension edge)) :
    control d hslots edge k axis i=
      Networks.BinaryRowProgram.run (Networks.ComplexPhaseRowSchedule.word edge)
        (originalCoordinates d hslots k axis) (slot edge i) := by
  have h := congrFun (coordinate_run d hslots edge k axis) (finCongr hslots.symm (slot edge i))
  simpa only [control,BinaryRowColumns.coordinates,Function.comp_apply,finCongr_apply,Fin.val_cast,
    Fin.cast_cast,Fin.cast_eq_self] using h

/-- The physically computed scalar is the original bilinear phase control. -/
theorem bilinear_control (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (k : Fin (d.rows*s.recordWidth)) (axis : Fin d.stage.f) (i : Fin (dimension edge)) :
    control d hslots edge k axis i=Labels.binary (25^3)
      (Networks.BinaryPhaseResidualRowProgram.basis Networks.ComplexPhaseBudget.coordinateSymm
        (low edge) (high edge) (low_nondegenerate edge) (high_nondegenerate edge)
        (comparable edge) (residual_good edge) i) (originalCoordinates d hslots k axis) := by
  rw [computed_control]
  exact Networks.BinaryPhaseResidualRowProgram.selected Networks.ComplexPhaseBudget.coordinateSymm
    (low edge) (high edge) (low_nondegenerate edge) (high_nondegenerate edge)
    (comparable edge) (residual_good edge) _ i

def diagonal (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (k : Fin (d.rows*s.recordWidth)) (axis : Fin d.stage.f) :=
  ∑ i : Fin (dimension edge), BinaryPhase.weightPhase
    (Networks.BinaryPhaseResidualRowProgram.basis Networks.ComplexPhaseBudget.coordinateSymm
      (low edge) (high edge) (low_nondegenerate edge) (high_nondegenerate edge)
      (comparable edge) (residual_good edge) i : Fin (25^3) → ZMod 2)*
    BinaryPhase.bitLift (control d hslots edge k axis i)

theorem phase (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (k : Fin (d.rows*s.recordWidth)) (axis : Fin d.stage.f) :
    BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) Networks.ComplexPhaseBudget.coordinateSymm
      (high edge) (high_nondegenerate edge) (originalCoordinates d hslots k axis))-
    BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) Networks.ComplexPhaseBudget.coordinateSymm
      (low edge) (low_nondegenerate edge) (originalCoordinates d hslots k axis))=
      diagonal d hslots edge k axis := by
  simpa only [diagonal,computed_control] using Networks.ComplexPhaseRowSchedule.phase edge (originalCoordinates d hslots k axis)

theorem original_phase (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge)
    (k : Fin (d.rows*s.recordWidth)) (axis : Fin d.stage.f) :
    BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) Networks.ComplexPhaseBudget.coordinateSymm
      (target edge) (target_nondegenerate edge) (originalCoordinates d hslots k axis))-
    BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) Networks.ComplexPhaseBudget.coordinateSymm
      (source edge) (source_nondegenerate edge) (originalCoordinates d hslots k axis))=
      if direction edge then -(diagonal d hslots edge k axis) else diagonal d hslots edge k axis := by
  rw [Networks.ComplexPhaseRowSchedule.original_phase,phase]

/-- Every payload cell follows the actual physical address compiler. -/
theorem entry (d : Inputs s) (hslots : d.stage.slots=25^3) (edge : Edge) (x : Array s d.rows)
    (k : Fin (d.rows*s.recordWidth)) :
    ActivePrefixStagePairSchedule.result d (word d hslots edge) x (destination d hslots edge k)=x k :=
  ActivePrefixStagePairCoordinates.run_entry d _ x k

end
end IntegerMultBounds.Machine.CompactComplexPhasePhysical
