module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOpsStock
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! Simultaneous storage bound for owned-prefix retirement; suffixes survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem retireCountedLine_native (rows width src count trash tmp : Fin T) :
    mnNativePushBound 3 (retireCountedLine (P := P) (Q := Q) (A := A) (U := U) rows width src count trash tmp) := by
  refine ⟨mnNativePushBound_mono (by decide) (unaryProduct_native _ _ _ _ _),?_,?_⟩
  · simp [discardPrefix,transfer,transferAct,uclear,moveR,moveStep,scanR,drainR,popDo,keepIn,
      whileR,peekR,mnNativePushBound,mnActPush]
  · simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

theorem retireCountedLine_exec_within (rows width src count trash tmp : Fin T)
    (hreg : [rows,width,src,count,trash,tmp].Nodup) (s w : ℕ) (residual tail : List (Fin (A+4)))
    (hlen : residual.length = s*w) (v : HS T Q A U) (S : Stacks T A)
    (hs : (S.R rows).length = s) (hw : (S.R width).length = w)
    (hsource : S.R src = residual++tail)
    (hcount : S.R count = []) (htrash : S.R trash = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retireCountedLineCost s w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+3*retireCountedLineCost s w) depth
        (retireCountedLine rows width src count trash tmp) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R src tail}) := by
  obtain ⟨v',n,hu,hn,he⟩ := retireCountedLine_exec (body := body) rows width src count trash tmp
    hreg s w residual tail hlen v S hs hw hsource hcount htrash htmp
  exact ⟨v',n,hu,hn,mn_native_exec_within he 3 (retireCountedLine_native ..) depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
