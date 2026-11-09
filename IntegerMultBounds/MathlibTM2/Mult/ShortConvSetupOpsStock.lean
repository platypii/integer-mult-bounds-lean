module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Native resource certificates for shared unary setup primitives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem unaryProduct_native (a b dst tmp saved : Fin T) :
    mnNativePushBound 2 (unaryProduct (P := P) (Q := Q) (A := A) (U := U) a b dst tmp saved) := by
  simp [unaryProduct,scanP,popPush,drainR,popDo,ucopy,umulSym,scanR,keepIn,pushN,
    moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
