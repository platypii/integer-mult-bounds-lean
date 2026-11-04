module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedPrefixPadding
public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTilePaddingData

/-! The existing owned-prefix padding has a native execution-wide bound.
Its counters and scratch are restored by the same execution certificate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem ownedPrefixPadding_native (exponent width src pad tmp saved : Fin T) (fill : Fin (A+4)) :
    mnNativePushBound 2 (ownedPrefixPadding (P := P) (Q := Q) (A := A) (U := U)
      exponent width src pad tmp saved fill) := by
  simp [ownedPrefixPadding,padding,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
    upow2,scanP,popPush,udbl,usub,dropTop,moveR,whileR,moveStep,peekR,
    mnNativePushBound,mnActPush]

theorem ownedPrefixPadding_exec_within (body : P → Pr P T Q A U)
    (exponent width src pad tmp saved : Fin T)
    (hreg : [exponent,width,src,pad,tmp,saved].Nodup) (fill : Fin (A+4))
    (l w : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hl : (S.R exponent).length = l) (hw : (S.R width).length = w)
    (hpad : S.R pad = []) (htmp : S.R tmp = []) (hsaved : S.R saved = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6*(2^l*w)+4*(S.R src).length+4*w+9*l+14 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*(6*(2^l*w)+4*(S.R src).length+4*w+9*l+14)) depth
        (ownedPrefixPadding exponent width src pad tmp saved fill) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          (tilePrefixPad (2^l*w) fill (S.R src)))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := ownedPrefixPadding_exec exponent width src pad tmp saved hreg fill
    l w v S hl hw hpad htmp hsaved
  exact ⟨v',n,hu,hn,mn_native_exec_within he 2 (ownedPrefixPadding_native _ _ _ _ _ _ _) depth _
    (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
