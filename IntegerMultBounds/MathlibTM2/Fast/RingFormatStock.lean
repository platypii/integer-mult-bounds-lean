module

public import IntegerMultBounds.MathlibTM2.Fast.RingProd
public import IntegerMultBounds.MathlibTM2.Host.AutoStock

/-! Native coefficient converters use the generic word-automaton push bound.
Their linear execution budgets therefore bound every intermediate store. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type}

private theorem rpWord_native (rg : RpReg → Fin T) {ni no : ℕ} [NeZero ni]
    (ins : Fin ni → RpReg) (outs : Fin no → RpReg) (M : Auto A ni no) (hno : no ≤ 3) :
    mnNativePushBound 3 (rpWord (P := P) (Q := Q) (A := A) (U := U) rg ins outs M) := by
  refine ⟨?_,autoWord_native _ _ _ _ _ _ _ (by decide) hno⟩
  simp [autoReset,peekR,mnNativePushBound,mnActPush]

theorem rpEnc_native (rg : RpReg → Fin T) (src dst : RpReg) :
    mnNativePushBound 3 (rpEnc (P := P) (Q := Q) (A := A) (U := U) rg src dst) := by
  simp only [rpEnc,rpWhile,rpEncBody,mnNativePushBound]
  refine ⟨⟨?_,⟨rpWord_native rg _ _ _ (by decide),?_,?_⟩,?_⟩,?_,?_⟩
  all_goals simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem rpDec_native (rg : RpReg → Fin T) :
    mnNativePushBound 3 (rpDec (P := P) (Q := Q) (A := A) (U := U) rg) := by
  simp only [rpDec,rpWhile,rpDecBody,mnNativePushBound]
  refine ⟨⟨?_,⟨rpWord_native rg _ _ _ (by decide),rpWord_native rg _ _ _ (by decide),
    rpWord_native rg _ _ _ (by decide)⟩,?_⟩,?_⟩
  all_goals simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Fast
