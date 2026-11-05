module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerBoundaryGeometryWords

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node CommonClassGeometry ScalarPlacement
  ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T A s : ℕ}
noncomputable section

def callerPreparedBoundaryState (widthSource : Fin T) (p s width : ℕ)
    (S : Stacks (MachineTapes T) A) : Stacks (MachineTapes T) A :=
  callerBoundaryGeometryState widthSource s width (2*p+13)
    {S with R := Function.update S.R (fullHeader T (.publication 3)) (List.replicate (2*p+13) tick)}

/-- Archiving in header 6 leaves all eleven loader sources untouched. -/
theorem seamMasterSources_ne_archive (src : Fin 11 → Fin T) (widthSource : Fin T) (i : Fin 11) :
    Fin.castAdd tapeCount (seamMasterSources T src widthSource i) ≠ fullHeader T (.publication 6) := by
  have hraw (j : Fin T) : Fin.castAdd tapeCount (Fin.castAdd 175 (bank id j)) ≠
      fullHeader T (.publication 6) := (fullHeader_ne_bank id (.publication 6) j).symm
  have hheader (r : Role) (hr : r ≠ .publication 6) :
      Fin.castAdd tapeCount (Fin.castAdd 175 (header T r)) ≠ fullHeader T (.publication 6) :=
    (fullHeader_injective T).ne hr
  fin_cases i
  all_goals first
    | exact hraw _
    | exact hheader _ (by simp)

/-- Header costs do not depend on the archive that the solver produced. -/
theorem seamMasterCopies_archive_map (source destination : Fin ((T+headerCount)+175))
    (src : Fin 11 → Fin T) (widthSource : Fin T) (S : Stacks (MachineTapes T) A)
    (archive : List (Fin (A+4))) (f : List (Fin (A+4)) → ℕ) :
    (boundarySeamMasterCopies source destination (seamMasterSources T src widthSource)).map
      (fun pair => f (Function.update S.R (fullHeader T (.publication 6)) archive pair.1)) =
    (boundarySeamMasterCopies source destination (seamMasterSources T src widthSource)).map
      (fun pair => f (S.R pair.1)) := by
  apply List.map_congr_left
  intro pair hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  rw [Function.update_of_ne (seamMasterSources_ne_archive src widthSource i)]

theorem callerPreparedBoundaryState_masterWords (p u l target t B W D N radius width : ℕ)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (seedValue : Fin 117 → ℕ)
    (hseed : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (S : Stacks (MachineTapes T) A)
    (hraw : ∀ i, (S.R (unarySource T (src i))).length = globalValues p u l target s t B W N radius width i)
    (hD : (S.R (unarySource T widthSource)).length = D)
    (hscalars : ∀ i, S.R (globals T i) = binSyms D (globalValues p u l target s t B W N radius width i))
    (archive : List (Fin (A+4))) :
    let F := callerPreparedBoundaryState widthSource p s width S
    BoundarySeamHeaderWords (s := s) p width W D N seedValue
      (fun i => Function.update F.R (fullHeader T (.publication 6)) archive
        (Fin.castAdd tapeCount (seamMasterSources T src widthSource i))) := by
  dsimp only
  let M : Stacks (MachineTapes T) A :=
    {S with R := Function.update S.R (fullHeader T (.publication 3)) (List.replicate (2*p+13) tick)}
  have hread (i : Fin (MachineTapes T)) (hi : i ≠ fullHeader T (.publication 3)) : M.R i = S.R i := by
    dsimp only [M]
    exact Function.update_of_ne hi _ _
  have hwords := callerBoundaryGeometryState_masterWords p u l target t B W D N radius width src widthSource
    seedValue hseed M
    (by intro i; exact (congrArg List.length (hread (unarySource T (src i))
      (fullHeader_ne_bank id (.publication 3) (src i)).symm)).trans (hraw i))
    (by exact (congrArg List.length (hread (unarySource T widthSource)
      (fullHeader_ne_bank id (.publication 3) widthSource).symm)).trans hD)
    (by intro i; exact (hread (globals T i) ((fullHeader_injective T).ne (by intro h; cases h))).trans (hscalars i))
    (by simp [M])
  have hframe : (fun i => Function.update (callerPreparedBoundaryState widthSource p s width S).R
      (fullHeader T (.publication 6)) archive (Fin.castAdd tapeCount (seamMasterSources T src widthSource i))) =
      (fun i => (callerPreparedBoundaryState widthSource p s width S).R
        (Fin.castAdd tapeCount (seamMasterSources T src widthSource i))) := by
    funext i
    exact Function.update_of_ne (seamMasterSources_ne_archive src widthSource i) _ _
  rw [hframe]
  exact hwords

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
