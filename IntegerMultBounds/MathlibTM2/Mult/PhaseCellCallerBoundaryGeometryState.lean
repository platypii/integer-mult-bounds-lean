module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerBoundaryGeometryPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryGeometryWrites

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds.MathlibTM2.Host ScalarPlacement
  ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T A : ℕ}
noncomputable section

/-- Joint controls in shared caller headers; all other tape banks are retained. -/
def callerBoundaryGeometryState (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) : Stacks (MachineTapes T) A :=
  rightUpdates ((boundaryGeometryWrites s width w [0,1,2]).map
    (fun (i,xs) => (boundaryGeometryRegister T widthSource i,xs))) S

theorem callerBoundaryGeometryState_off (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) (i : Fin (MachineTapes T))
    (hskip : ∀ slot, boundaryGeometryRegister T widthSource (boundarySeamCropSkip slot) ≠ i)
    (hcount : ∀ slot, boundaryGeometryRegister T widthSource (boundarySeamCropCount slot) ≠ i) :
    (callerBoundaryGeometryState widthSource s width w S).R i = S.R i :=
  rightUpdates_boundaryGeometryWrites_off _ _ _ _ _ _ _ hskip hcount

theorem callerBoundaryGeometryState_updateR (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) (i : Fin (MachineTapes T)) (xs : List (Fin (A+4)))
    (hskip : ∀ slot, boundaryGeometryRegister T widthSource (boundarySeamCropSkip slot) ≠ i)
    (hcount : ∀ slot, boundaryGeometryRegister T widthSource (boundarySeamCropCount slot) ≠ i) :
    callerBoundaryGeometryState widthSource s width w {S with R := Function.update S.R i xs} =
      {callerBoundaryGeometryState widthSource s width w S with R :=
        (Function.update (callerBoundaryGeometryState widthSource s width w S).R i xs)} :=
  rightUpdates_boundaryGeometryWrites_updateR _ _ _ _ _ _ _ _ hskip hcount

theorem callerBoundaryGeometryState_zero (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) (hzero : S.R (fullHeader T .zero) = []) :
    (callerBoundaryGeometryState widthSource s width w S).R (fullHeader T .zero) =
      S.R (fullHeader T .zero) := by
  simp only [callerBoundaryGeometryState,boundaryGeometryWrites,List.map_cons,List.map_nil,
    rightUpdates]
  change (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update S.R (boundaryGeometryRegister T widthSource (boundarySeamCropSkip 0)) _)
      (boundaryGeometryRegister T widthSource (boundarySeamCropCount 0)) _)
      (boundaryGeometryRegister T widthSource (boundarySeamCropSkip 1)) _)
      (boundaryGeometryRegister T widthSource (boundarySeamCropCount 1)) _)
      (boundaryGeometryRegister T widthSource (boundarySeamCropSkip 2)) _)
      (boundaryGeometryRegister T widthSource (boundarySeamCropCount 2)) _) (fullHeader T .zero) = _
  rw [boundaryGeometryRegister_zero,boundaryGeometryRegister_skip_one,
    boundaryGeometryRegister_skip_two,boundaryGeometryRegister_count,
    boundaryGeometryRegister_count,boundaryGeometryRegister_count]
  simp [(fullHeader_injective T).eq_iff,IntegerMultBounds.NLogN.PhaseCellMatrix.coreStart,
    IntegerMultBounds.NLogN.PhaseCellMatrix.boundaryCropIndex,hzero]

theorem callerBoundaryGeometryState_private (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) (i : Fin tapeCount) :
    (callerBoundaryGeometryState widthSource s width w S).R
      (Fin.natAdd ((T+headerCount)+175) i) = S.R (Fin.natAdd ((T+headerCount)+175) i) := by
  apply rightUpdates_boundaryGeometryWrites_off
  · intro slot
    fin_cases slot
    · change boundaryGeometryRegister T widthSource (boundarySeamCropSkip 0) ≠ _
      rw [boundaryGeometryRegister_zero]
      exact prefix_ne_routing _ _
    · change boundaryGeometryRegister T widthSource (boundarySeamCropSkip 1) ≠ _
      rw [boundaryGeometryRegister_skip_one]
      exact prefix_ne_routing _ _
    · change boundaryGeometryRegister T widthSource (boundarySeamCropSkip 2) ≠ _
      rw [boundaryGeometryRegister_skip_two]
      exact prefix_ne_routing _ _
  · intro slot
    rw [boundaryGeometryRegister_count]
    exact prefix_ne_routing _ _

theorem callerBoundaryGeometryState_eq (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) :
    embOvr (boundaryGeometryRegister T widthSource)
      (exportBoundaryGeometryState s width w [0,1,2]
        (embStk (boundaryGeometryRegister T widthSource) S)).get S =
      callerBoundaryGeometryState widthSource s width w S :=
  embOvr_exportBoundaryGeometryState _ (boundaryGeometryRegister_injective T widthSource) _ _ _ _ _

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
