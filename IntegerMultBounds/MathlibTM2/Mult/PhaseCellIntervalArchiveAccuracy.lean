module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalArchive
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Complex recovery accuracy survives the existing crop-and-retire archive
loop, in precisely the reverse order written to the destination. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {A s : ℕ} [NeZero s]

/-- Cropping changes the stored interval but adds no complex numerical error. -/
theorem packedInterval_crop_error (q w a L offset length : ℕ)
    (hfit : a+L ≤ s) (hpart : offset+length ≤ L) (D : ZMod s → GaussianInt)
    (sourceTail outputTail : List (Fin (A+4))) (z : ZMod s → ℂ) (ε : ℝ)
    (hgood : PhaseCellInterface.ErrorOn (haloVertices s a (a+L))
      (packedIntervalRead q w a (cstream A w (packedInterval a L D)++sourceTail)) z ε) :
    PhaseCellInterface.ErrorOn (haloVertices s (a+offset) (a+offset+length))
      (packedIntervalRead q w (a+offset)
        (cstream A w (packedInterval (a+offset) length D)++outputTail)) z ε := by
  intro i hi
  obtain ⟨hi₁,hi₂⟩ := (mem_haloVertices _ _ i).mp hi
  have h := hgood i ((mem_haloVertices _ _ i).mpr ⟨by omega,by omega⟩)
  rw [packedIntervalRead_eq q w (a+offset) length D outputTail [] (by omega) i hi₁ hi₂]
  rw [packedIntervalRead_eq q w a L D sourceTail [] hfit i (by omega) (by omega)] at h
  exact h

variable {T Q : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Reuse the physical interval archive unchanged. The returned complex
certificate follows its actual destination packet order and arbitrary suffix. -/
theorem packedCoreArchiveLoop_interval_accurate_exec
    (clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [clock,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (q w a L offset length : ℕ)
    (hfit : a+L ≤ s) (hpart : offset+length ≤ L)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (ε : ℝ)
    (tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s a (a+L))
      (packedIntervalRead q w a (cstream A w (packedInterval a L D)++tail)) z ε) Zs Ds)
    (hsrc : S.R src = (Ds.map (fun D => cstream A w (packedInterval a L D))).flatten++tail)
    (hclock : (S.R clock).length = Ds.length) (hskip : (S.R skip).length = offset*w)
    (hcount : (S.R count).length = length*w) (hrows : (S.R rows).length = L)
    (hwidth : (S.R width).length = w)
    (hclean : ∀ i ∈ [savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ Ds.length*(packedCoreArchiveStepCost offset length L w+3)+2 ∧
      Exec body (packedCoreArchiveLoop clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (Host.mk v S) n (Host.mk v' F) ∧
      F.R src = tail ∧ F.R dst = (Ds.reverse.map (fun D => cstream A w
        (packedInterval (a+offset) length D))).flatten++S.R dst ∧
      F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
        (haloVertices s (a+offset) (a+offset+length))
        (packedIntervalRead q w (a+offset)
          (cstream A w (packedInterval (a+offset) length D)++S.R dst)) z ε) Zs.reverse Ds.reverse := by
  obtain ⟨v',F,n,hu,hn,hex,hs,hd,hc,hi,ho,hl,hframe⟩ := packedCoreArchiveLoop_interval_exec
    (body := body) clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp
    hreg v S w a L offset length hfit hpart Ds tail hsrc hclock hskip hcount hrows hwidth hclean
  refine ⟨v',F,n,hu,hn,hex,hs,hd,hc,hi,ho,hl,hframe,?_⟩
  apply List.forall₂_reverse_iff.mpr
  exact hgood.imp (fun z D h => packedInterval_crop_error q w a L offset length hfit hpart D tail (S.R dst) z ε h)

omit [NeZero s] in
theorem packedCoreArchiveLoop_interval_native
    (clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T) :
    mnNativePushBound 2 (packedCoreArchiveLoop (P := P) (Q := Q) (A := A) (U := U)
      clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp) := by
  simp [packedCoreArchiveLoop,packedCoreArchiveStep,copySlice,copyPrefix,copyR,copyStep,
    retireCountedLine,discardPrefix,countedLoopBody,countedLoop,unaryProduct,scanP,ucopy,umulSym,
    transfer,moveR,uclear,keepIn,scanR,transferAct,drainR,popDo,whileR,moveStep,peekR,pushN,popPush,
    mnNativePushBound,mnActPush]

omit [NeZero s] in
/-- Cropping and retiring an archive use stock linear in its encoded volume. -/
theorem packedCoreArchiveLoop_interval_within_stock
    {clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T}
    {v v' : HS T Q A U} {S F : Stacks T A} {n N offset length L w : ℕ}
    (hex : Exec body
      (packedCoreArchiveLoop clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
      (Host.mk v S) n (Host.mk v' F))
    (hn : n ≤ N*(packedCoreArchiveStepCost offset length L w+3)+2) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
      2*(N*(packedCoreArchiveStepCost offset length L w+3)+2)) depth
      (packedCoreArchiveLoop clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
      (Host.mk v S) n (Host.mk v' F) :=
  mn_native_exec_within hex 2 (packedCoreArchiveLoop_interval_native _ _ _ _ _ _ _ _ _ _ _ _ _)
    depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
