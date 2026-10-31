module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Structural push bounds for unary header export from a retained binary table. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A n : ℕ} {P U : Type}

theorem tblUnaryCopies_native (rg : TblR n → Fin T) (ls : List (Fin n × Fin T)) :
    mnNativePushBound 3 (tblUnaryCopies (P := P) (Q := Q) (A := A) (U := U) rg ls) := by
  induction ls with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    refine ⟨?_,ih⟩
    simp [toUnary,eachSym,hornerIter,udbl,drainR,popDo,pushN,
      moveR,moveStep,whileR,peekR,popPush,mnNativePushBound,mnActPush]
end IntegerMultBounds.MathlibTM2.Mult.ShortConv
