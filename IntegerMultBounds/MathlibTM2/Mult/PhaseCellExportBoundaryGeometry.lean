module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedStandardBoundaryCounters
public import IntegerMultBounds.MathlibTM2.Host.MoveGeneratedWord

/-! Export both narrow crop controls from one restored metadata computation.
The arithmetic bank and both temporary exports return to their original state. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix BoundaryCropMetadata
variable {Q A : ℕ} {P U : Type}

def exportBoundaryGeometry (last : Bool) (skipDst countDst : Fin 117) : Pr P 117 Q A U :=
  .seq (preparedStandardBoundaryCounters last) (moveGeneratedPair 26 24 skipDst countDst)

def exportBoundaryGeometryCost (last : Bool) (D s width w : ℕ) : ℕ :=
  (64*D+81)+(16*tblC D 0+6*(s*w)+22*D+13)+(20*D+21)+
    (2*(coreStart width (index last s width)*w)+2*(coreLength s width (index last s width)*w)+4)

theorem exportBoundaryGeometry_exec (body : P → Pr P 117 Q A U)
    (last : Bool) (skipDst countDst : Fin 117) (hreg : [26,24,skipDst,countDst].Nodup)
    (D s width w : ℕ) (hw : 0 < width) (hword : 0 < w) (hroom : 3*width < s)
    (hvolumeFit : s*w < 2^D) (value : Fin 117 → ℕ)
    (hvalues : ∀ j, value (boundarySeedGlobals j) = ![s,width,w] j)
    (hfit : ∀ j, value (boundarySeedGlobals j) < 2^D)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hwidth : (S.R 58).length = D) (hzero : S.R 59 = [])
    (hwords : ∀ j, S.R (boundarySeedGlobals j) = binSyms D (value (boundarySeedGlobals j)))
    (hblank : ∀ r, S.R (boundaryCounterRegister r) = [])
    (hmasters : S.R 26 = [] ∧ S.R 24 = [])
    (houtputs : S.R skipDst = [] ∧ S.R countDst = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ exportBoundaryGeometryCost last D s width w ∧
      Exec body (exportBoundaryGeometry last skipDst countDst) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R skipDst
          (List.replicate (coreStart width (index last s width)*w) tick)) countDst
          (List.replicate (coreLength s width (index last s width)*w) tick))}) := by
  obtain ⟨u,a,hu,ha,he⟩ := preparedStandardBoundaryCounters_exec body last D s width w hw hword hroom
    hvolumeFit value hvalues hfit v S hwidth hzero hwords hblank hmasters depth
  obtain ⟨v',hv,hmove⟩ := moveGeneratedPair_exec body 26 24 skipDst countDst hreg
    (List.replicate (coreStart width (index last s width)*w) tick)
    (List.replicate (coreLength s width (index last s width)*w) tick) u S
    ⟨hmasters.1,hmasters.2,houtputs.1,houtputs.2⟩
  simp only [List.length_replicate,List.reverse_replicate] at hmove
  refine ⟨v',a+((2*(coreStart width (index last s width)*w)+2)+
    (2*(coreLength s width (index last s width)*w)+2)),hv.trans hu,?_,?_⟩
  · unfold exportBoundaryGeometryCost
    omega
  · exact Exec.seq he hmove

theorem exportBoundaryGeometry_native (last : Bool) (skipDst countDst : Fin 117) :
    mnNativePushBound 3
      (exportBoundaryGeometry (P := P) (Q := Q) (A := A) (U := U) last skipDst countDst) := by
  refine ⟨preparedStandardBoundaryCounters_native last,?_⟩
  simp [moveGeneratedPair,moveR,moveStep,whileR,drainR,popDo,popPush,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
