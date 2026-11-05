module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportBoundaryGeometry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportBoundaryCountsStock

/-! One fixed-slot interface for physical crop-count generation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type}

/-- The first skip uses a retained zero port; final skips have their own ports. -/
def boundarySeamCropSkip (slot : Fin 3) : Fin 117 :=
  if slot = 0 then 65 else ⟨62+slot.val,by omega⟩

def exportSlotBoundaryGeometry (slot : Fin 3) : Pr P 117 Q A U :=
  if slot = 0 then exportFirstBoundaryCount (boundarySeamCropCount slot)
  else exportBoundaryGeometry (decide (slot = 2)) (boundarySeamCropSkip slot) (boundarySeamCropCount slot)

theorem exportSlotBoundaryGeometry_exec (body : P → Pr P 117 Q A U)
    (slot : Fin 3) (D s width w : ℕ) (hw : 0 < width) (hword : 0 < w)
    (hroom : 3*width < s) (hvolumeFit : s*w < 2^D) (value : Fin 117 → ℕ)
    (hvalues : ∀ j, value (boundarySeedGlobals j) = ![s,width,w] j)
    (hfit : ∀ j, value (boundarySeedGlobals j) < 2^D)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hwidth : (S.R 58).length = D) (hzero : S.R 59 = [])
    (hwords : ∀ j, S.R (boundarySeedGlobals j) = binSyms D (value (boundarySeedGlobals j)))
    (hblank : ∀ r, S.R (boundaryCounterRegister r) = [])
    (hmasters : S.R 26 = [] ∧ S.R 24 = [])
    (hwide : (S.R 17).length = w) (htmp : S.R 27 = []) (hsaved : S.R 28 = [])
    (hskip : S.R (boundarySeamCropSkip slot) = []) (hdst : S.R (boundarySeamCropCount slot) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ exportSlotBoundaryCountCost slot D s width w ∧
      Exec body (exportSlotBoundaryGeometry slot) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R (boundarySeamCropSkip slot)
          (List.replicate (coreStart width (boundaryCropIndex s width slot)*w) Node.tick)) (boundarySeamCropCount slot)
          (List.replicate (coreLength s width (boundaryCropIndex s width slot)*w) Node.tick))}) := by
  have hlast (last : Bool) (hindex : BoundaryCropMetadata.index last s width = boundaryCropIndex s width slot) :=
    exportBoundaryGeometry_exec body last (boundarySeamCropSkip slot) (boundarySeamCropCount slot) (by
      fin_cases slot <;> decide +kernel) D s width w hw hword hroom hvolumeFit value hvalues hfit
      v S hwidth hzero hwords hblank hmasters ⟨hskip,hdst⟩ depth
  fin_cases slot
  · have hbinary : S.R 56 = binSyms D width := by
      have h := hwords 1
      rw [hvalues 1] at h
      simpa [boundarySeedGlobals] using h
    have hwidthFit : width < 2^D := by
      have h := hfit 1
      rw [hvalues 1] at h
      exact h
    obtain ⟨v',n,hu,hn,he⟩ := exportFirstBoundaryCount_exec body (boundarySeamCropCount 0)
      (by decide +kernel) D width w hwidthFit v S hbinary hwide hdst hmasters.1
      ⟨hblank (.v 0),hblank (.v 1),hblank (.v 2),htmp,hsaved⟩
    have hskipSelf : Function.update S.R 65 [] = S.R := by
      rw [←show S.R 65 = [] from hskip]
      exact Function.update_eq_self _ _
    refine ⟨v',n,hu,hn,?_⟩
    simpa [exportSlotBoundaryGeometry,boundarySeamCropSkip,boundaryCropIndex,coreStart,coreLength,hskipSelf,
      Nat.min_eq_left (show width ≤ s by omega)] using he
  · have hi := BoundaryCropMetadata.index_eq_boundary false s width hw hroom
    have h := hlast false (by simpa using hi)
    simpa [exportSlotBoundaryGeometry,exportSlotBoundaryCountCost,exportBoundaryGeometryCost,hi] using h
  · have hi := BoundaryCropMetadata.index_eq_boundary true s width hw hroom
    have h := hlast true (by simpa using hi)
    simpa [exportSlotBoundaryGeometry,exportSlotBoundaryCountCost,exportBoundaryGeometryCost,hi] using h

theorem exportSlotBoundaryGeometry_native (slot : Fin 3) :
    mnNativePushBound 3 (exportSlotBoundaryGeometry (P := P) (Q := Q) (A := A) (U := U) slot) := by
  unfold exportSlotBoundaryGeometry
  split
  · exact exportFirstBoundaryCount_native _
  · exact exportBoundaryGeometry_native _ _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
