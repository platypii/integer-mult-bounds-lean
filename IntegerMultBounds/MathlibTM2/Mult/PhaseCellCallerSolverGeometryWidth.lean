module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolverSeparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolverWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerBoundaryGeometryState

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds.MathlibTM2.Host ScalarPlacement
variable {T A : ℕ}
noncomputable section

theorem callerSolverGeometry_ports_ne (widthSource : Fin (T+solverRegisterCount))
    (i : Fin (MachineTapes (T+solverRegisterCount)))
    (hheader : ∀ r, fullHeader (T+solverRegisterCount) r ≠ i) :
    (∀ slot, boundaryGeometryRegister _ widthSource (boundarySeamCropSkip slot) ≠ i) ∧
    (∀ slot, boundaryGeometryRegister _ widthSource (boundarySeamCropCount slot) ≠ i) := by
  constructor
  · intro slot
    fin_cases slot
    · change boundaryGeometryRegister _ widthSource (boundarySeamCropSkip 0) ≠ _
      rw [boundaryGeometryRegister_zero]
      exact hheader .zero
    · change boundaryGeometryRegister _ widthSource (boundarySeamCropSkip 1) ≠ _
      rw [boundaryGeometryRegister_skip_one]
      exact hheader (.publication 4)
    · change boundaryGeometryRegister _ widthSource (boundarySeamCropSkip 2) ≠ _
      rw [boundaryGeometryRegister_skip_two]
      exact hheader (.publication 5)
  · intro slot
    rw [boundaryGeometryRegister_count]
    exact hheader _

theorem callerSolverGeometry_ports_ne_register (widthSource : Fin (T+solverRegisterCount))
    (r : SolverRole) :
    (∀ slot, boundaryGeometryRegister _ widthSource (boundarySeamCropSkip slot) ≠ solverRegister T r) ∧
    (∀ slot, boundaryGeometryRegister _ widthSource (boundarySeamCropCount slot) ≠ solverRegister T r) :=
  callerSolverGeometry_ports_ne widthSource _ (fun h => (solverRegister_ne_header T r h).symm)

theorem callerSolverGeometry_off_source (widthSource : Fin (T+solverRegisterCount))
    (s width w : ℕ) (S : Stacks (MachineTapes (T+solverRegisterCount)) A) (i : Fin T) :
    (callerBoundaryGeometryState widthSource s width w S).R (unarySource _ (solverSource i)) =
      S.R (unarySource _ (solverSource i)) := by
  have h := callerSolverGeometry_ports_ne widthSource _ (fun r => solverHeader_ne_source T r i)
  exact callerBoundaryGeometryState_off widthSource s width w S _ h.1 h.2

theorem callerSolverGeometry_off_register (widthSource : Fin (T+solverRegisterCount))
    (s width w : ℕ) (S : Stacks (MachineTapes (T+solverRegisterCount)) A) (r : SolverRole) :
    (callerBoundaryGeometryState widthSource s width w S).R (solverRegister T r) =
      S.R (solverRegister T r) := by
  have h := callerSolverGeometry_ports_ne_register widthSource r
  exact callerBoundaryGeometryState_off widthSource s width w S _ h.1 h.2

theorem callerSolverGeometry_width (widthSource : Fin (T+solverRegisterCount))
    (s width w B : ℕ) (S : Stacks (MachineTapes (T+solverRegisterCount)) A) :
    callerBoundaryGeometryState widthSource s width w (callerSolverWidthState B S) =
      callerSolverWidthState B (callerBoundaryGeometryState widthSource s width w S) := by
  have h := callerSolverGeometry_ports_ne_register widthSource (.input (familyInverseScalarReg .wr))
  exact callerBoundaryGeometryState_updateR widthSource s width w S _ _ h.1 h.2

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
