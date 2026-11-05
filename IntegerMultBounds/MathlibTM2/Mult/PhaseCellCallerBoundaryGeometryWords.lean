module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerBoundaryGeometryState

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.NLogN.PhaseCellMatrix
  CommonClassGeometry ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
variable {T A s : ℕ}
noncomputable section

theorem callerBoundaryGeometryState_view (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) :
    embStk (boundaryGeometryRegister T widthSource) (callerBoundaryGeometryState widthSource s width w S) =
      exportBoundaryGeometryState s width w [0,1,2] (embStk (boundaryGeometryRegister T widthSource) S) := by
  rw [← callerBoundaryGeometryState_eq,embStk_ovr (boundaryGeometryRegister_injective T widthSource)]

theorem callerBoundaryGeometryState_count (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) (slot : Fin 3) :
    (callerBoundaryGeometryState widthSource s width w S).R
      (fullHeader T (.publication (Fin.castAdd 4 slot))) =
      List.replicate (coreLength s width (boundaryCropIndex s width slot)*w) tick := by
  have h := congrArg (fun B : Stacks 117 A => B.R (boundarySeamCropCount slot))
    (callerBoundaryGeometryState_view widthSource s width w S)
  change (callerBoundaryGeometryState widthSource s width w S).R
    (boundaryGeometryRegister T widthSource (boundarySeamCropCount slot)) = _ at h
  rw [boundaryGeometryRegister_count] at h
  exact h.trans (exportBoundaryGeometryState_count s width w [0,1,2] (by decide) _ slot
    (by fin_cases slot <;> simp))

theorem callerBoundaryGeometryState_word (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) :
    (callerBoundaryGeometryState widthSource s width w S).R (fullHeader T (.publication 3)) =
      S.R (fullHeader T (.publication 3)) := by
  have h := congrArg (fun B : Stacks 117 A => B.R 17)
    (callerBoundaryGeometryState_view widthSource s width w S)
  have hoff := exportBoundaryGeometryState_off s width w [0,1,2]
    (embStk (boundaryGeometryRegister T widthSource) S) 17 (by decide +kernel)
  simpa only [embStk,Function.comp_apply,boundaryGeometryRegister_word] using h.trans hoff

/-- Only publication ports and the empty zero source are written. -/
theorem callerBoundaryGeometryState_off_header_bank (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) (i : Fin (MachineTapes T))
    (hz : fullHeader T .zero ≠ i)
    (hp : ∀ j : Fin 6, fullHeader T (.publication (Fin.castAdd 1 j)) ≠ i) :
    (callerBoundaryGeometryState widthSource s width w S).R i = S.R i := by
  apply callerBoundaryGeometryState_off
  · intro slot
    fin_cases slot
    · change boundaryGeometryRegister T widthSource (boundarySeamCropSkip 0) ≠ _
      rw [boundaryGeometryRegister_zero]; exact hz
    · change boundaryGeometryRegister T widthSource (boundarySeamCropSkip 1) ≠ _
      rw [boundaryGeometryRegister_skip_one]; exact hp 4
    · change boundaryGeometryRegister T widthSource (boundarySeamCropSkip 2) ≠ _
      rw [boundaryGeometryRegister_skip_two]; exact hp 5
  · intro slot
    rw [boundaryGeometryRegister_count]; exact hp (Fin.castAdd 3 slot)

theorem callerBoundaryGeometryState_source (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) (i : Fin T) :
    (callerBoundaryGeometryState widthSource s width w S).R (unarySource T i) = S.R (unarySource T i) :=
  callerBoundaryGeometryState_off_header_bank widthSource s width w S _
    (fullHeader_ne_bank id .zero i) (fun j => fullHeader_ne_bank id (.publication (Fin.castAdd 1 j)) i)

theorem callerBoundaryGeometryState_scalar (widthSource : Fin T) (s width w : ℕ)
    (S : Stacks (MachineTapes T) A) (i : Fin 11) :
    (callerBoundaryGeometryState widthSource s width w S).R (globals T i) = S.R (globals T i) :=
  callerBoundaryGeometryState_off_header_bank widthSource s width w S _
    ((fullHeader_injective T).ne (by intro h; cases h))
    (fun j => (fullHeader_injective T).ne (by intro h; cases h))

/-- The generated control words meet the existing publication loader contract. -/
theorem callerBoundaryGeometryState_masterWords (p u l target t B W D N radius width : ℕ)
    (src : Fin 11 → Fin T) (widthSource : Fin T) (seedValue : Fin 117 → ℕ)
    (hseed : ∀ j, seedValue (boundarySeedGlobals j) = ![s,width,W] j)
    (S : Stacks (MachineTapes T) A)
    (hraw : ∀ i, (S.R (unarySource T (src i))).length = globalValues p u l target s t B W N radius width i)
    (hD : (S.R (unarySource T widthSource)).length = D)
    (hscalars : ∀ i, S.R (globals T i) = binSyms D (globalValues p u l target s t B W N radius width i))
    (hword : (S.R (fullHeader T (.publication 3))).length = 2*p+13) :
    BoundarySeamHeaderWords (s := s) p width W D N seedValue
      (fun i => (callerBoundaryGeometryState widthSource s width (2*p+13) S).R
        (Fin.castAdd tapeCount (seamMasterSources T src widthSource i))) := by
  apply seamMasterSources_headerWords p u l target t B W D N radius width src widthSource seedValue hseed
  · intro i
    rw [callerBoundaryGeometryState_source]; exact hraw i
  · rw [callerBoundaryGeometryState_source]; exact hD
  · intro i
    rw [callerBoundaryGeometryState_scalar]; exact hscalars i
  · rw [callerBoundaryGeometryState_word]; exact hword
  · intro slot
    rw [callerBoundaryGeometryState_count,List.length_replicate]

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
