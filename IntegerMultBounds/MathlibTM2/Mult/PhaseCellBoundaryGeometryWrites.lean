module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportBoundaryGeometrySequence
public import IntegerMultBounds.MathlibTM2.Host.RightUpdates

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T A : ℕ}

/-- Each slot contributes its skip followed by its retained crop count. -/
def boundaryGeometryWrites (s width w : ℕ) : List (Fin 3) → List (Fin 117 × List (Fin (A+4)))
  | [] => []
  | slot::slots =>
    (boundarySeamCropSkip slot, List.replicate (coreStart width (boundaryCropIndex s width slot)*w) tick) ::
    (boundarySeamCropCount slot, List.replicate (coreLength s width (boundaryCropIndex s width slot)*w) tick) ::
    boundaryGeometryWrites s width w slots

theorem exportBoundaryGeometryState_eq_rightUpdates (s width w : ℕ) (slots : List (Fin 3))
    (S : Stacks 117 A) :
    exportBoundaryGeometryState s width w slots S = rightUpdates (boundaryGeometryWrites s width w slots) S := by
  induction slots generalizing S with
  | nil => rfl
  | cons slot slots ih =>
    exact ih _

/-- Only the six control ports affect the placed geometry endpoint. -/
theorem map_boundaryGeometryWrites (e f : Fin 117 → Fin T)
    (hskip : ∀ slot, e (boundarySeamCropSkip slot) = f (boundarySeamCropSkip slot))
    (hcount : ∀ slot, e (boundarySeamCropCount slot) = f (boundarySeamCropCount slot))
    (s width w : ℕ) (slots : List (Fin 3)) :
    (boundaryGeometryWrites (A := A) s width w slots).map (fun (i,xs) => (e i,xs)) =
      (boundaryGeometryWrites s width w slots).map (fun (i,xs) => (f i,xs)) := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    simp only [boundaryGeometryWrites,List.map_cons,hskip,hcount,ih]

theorem rightUpdates_boundaryGeometryWrites_off (e : Fin 117 → Fin T)
    (s width w : ℕ) (slots : List (Fin 3)) (S : Stacks T A) (i : Fin T)
    (hskip : ∀ slot, e (boundarySeamCropSkip slot) ≠ i)
    (hcount : ∀ slot, e (boundarySeamCropCount slot) ≠ i) :
    (rightUpdates ((boundaryGeometryWrites s width w slots).map
      (fun (j,xs) => (e j,xs))) S).R i = S.R i := by
  induction slots generalizing S with
  | nil => rfl
  | cons slot slots ih =>
    simp only [boundaryGeometryWrites,List.map_cons,rightUpdates]
    rw [ih]
    exact (Function.update_of_ne (hcount slot).symm ..).trans
      (Function.update_of_ne (hskip slot).symm ..)

/-- The endpoint of joint control generation transports through any injective
placement, including placements sharing the caller's retained headers. -/
theorem embOvr_exportBoundaryGeometryState (e : Fin 117 → Fin T) (he : Function.Injective e)
    (s width w : ℕ) (slots : List (Fin 3)) (S : Stacks T A) :
    embOvr e (exportBoundaryGeometryState s width w slots (embStk e S)).get S =
      rightUpdates ((boundaryGeometryWrites s width w slots).map (fun (i,xs) => (e i,xs))) S := by
  rw [exportBoundaryGeometryState_eq_rightUpdates, embOvr_rightUpdates he, embOvr_stk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
