module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateBoundaryCounts
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportBoundaryGeometrySequence

/-! Generate both skip/count controls for every crop from retained dimensions
and a unary word ruler, then retire the generated binary seed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type}

def generateBoundaryGeometry : Pr P 117 Q A U :=
  .seq narrowBoundarySeed (.seq (restoringSequence exportSlotBoundaryGeometry [0,1,2]) (uclear 57))

theorem generateBoundaryGeometry_exec (body : P → Pr P 117 Q A U)
    (D s width w : ℕ) (hw : 0 < width) (hword : 0 < w)
    (hroom : 3*width < s) (hvolumeFit : s*w < 2^D) (value : Fin 117 → ℕ)
    (hvalues : ∀ j, value (boundarySeedGlobals j) = ![s,width,w] j)
    (hfit : ∀ j, value (boundarySeedGlobals j) < 2^D)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hwidth : (S.R 58).length = D) (hzero : S.R 59 = [])
    (hwords : ∀ j : Fin 3, j ≠ 2 → S.R (boundarySeedGlobals j) = binSyms D (value (boundarySeedGlobals j)))
    (hblank : ∀ r, S.R (boundaryCounterRegister r) = [])
    (hmasters : S.R 26 = [] ∧ S.R 24 = [])
    (hwide : (S.R 17).length = w) (htmp : S.R 27 = []) (hsaved : S.R 28 = [])
    (hseed : S.R 57 = []) (hdst : ∀ slot, S.R (boundarySeamCropSkip slot) = [] ∧ S.R (boundarySeamCropCount slot) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (w*(4*D+10)+4*D+8)+boundaryCountExportCost D s width w+(2*D+2) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*(4*D+4)+3*boundaryCountExportCost D s width w)) depth
        generateBoundaryGeometry (mk v S) n
        (mk v' (exportBoundaryGeometryState s width w [0,1,2] S)) := by
  obtain ⟨u,a,hu,ha,he⟩ := narrowBoundarySeed_exec_within body D w v S hwide hwidth hseed htmp hsaved depth
  let M : Stacks 117 A := {S with R := Function.update S.R 57 (binSyms D w)}
  have hr : BoundaryCountReady D w value M := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [M] using hwidth
    · simpa [M] using hzero
    · intro j
      fin_cases j
      · simpa [M,boundarySeedGlobals] using hwords 0 (by decide)
      · simpa [M,boundarySeedGlobals] using hwords 1 (by decide)
      · have hvalue : value 57 = w := by simpa [boundarySeedGlobals] using hvalues 2
        simp [M,boundarySeedGlobals,hvalue]
    · intro r
      have hne : boundaryCounterRegister r ≠ 57 := by
        have hb := boundaryCounterRegister_bounds r
        intro heq
        have hv := congrArg Fin.val heq
        simp at hv
        omega
      simpa only [M,Function.update_of_ne hne] using hblank r
    · simpa [M] using hmasters
    · simpa [M] using hwide
    · simpa [M] using htmp
    · simpa [M] using hsaved
  obtain ⟨u',b,hu',hb,hx⟩ := exportBoundaryGeometrySequence_exec body D s width w hw hword hroom hvolumeFit
    value hvalues hfit [0,1,2] (by decide) u M hr (by
      intro slot hslot
      have hskip : boundarySeamCropSkip slot ≠ 57 := by
        have hb := (boundarySeamCropPorts_lower slot).1
        intro h; have hv := congrArg Fin.val h; simp at hv; omega
      have hcount : boundarySeamCropCount slot ≠ 57 := by
        have hb := (boundarySeamCropPorts_lower slot).2
        intro h; have hv := congrArg Fin.val h; simp at hv; omega
      simpa only [M,Function.update_of_ne hskip,Function.update_of_ne hcount] using hdst slot) depth
  have hb' : b ≤ boundaryCountExportCost D s width w := hb
  have hcounts := mn_native_exec_within hx 3 (exportBoundaryGeometrySequence_native [0,1,2]) depth
    (mnSize (mk u M)+depth+3*boundaryCountExportCost D s width w) (by omega)
  let F := exportBoundaryGeometryState s width w [0,1,2] M
  have hF57 : F.R 57 = binSyms D w := by
    rw [exportBoundaryGeometryState_off s width w [0,1,2] M 57 (by decide +kernel)]
    simp [M]
  obtain ⟨v',hv,hclear⟩ := uclear_exec (body := body) 57 u' F
  rw [hF57,length_binSyms] at hclear
  have hend : ({F with R := Function.update F.R 57 []} : Stacks 117 A) =
      exportBoundaryGeometryState s width w [0,1,2] S := by
    refine Stacks.ext (by rfl) (by rfl) (by rfl) ?_
    funext i
    simp only [F,M,exportBoundaryGeometryState,Function.update_apply]
    by_cases hi : i = 57
    · subst i; simp [boundarySeamCropCount,boundarySeamCropSkip,hseed]
    · simp [hi]
  rw [hend] at hclear
  have hclearNative : mnNativePushBound 0 (uclear (T := 117) (P := P) (Q := Q) (A := A) (U := U) 57) := by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]
  have hcleanup := mn_native_exec_within hclear 0 hclearNative depth (mnSize (mk u' F)+depth) (by omega)
  refine ⟨v',a+(b+(2*D+2)),hv.trans (hu'.trans hu),by omega,?_⟩
  have hs := he.final
  have hc := hcounts.final
  apply ExecWithin.seq (he.mono (by intro d z hz; omega))
  apply ExecWithin.seq (hcounts.mono (by intro d z hz; dsimp only [M] at *; omega))
  exact hcleanup.mono (by intro d z hz; dsimp only [F,M] at *; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
