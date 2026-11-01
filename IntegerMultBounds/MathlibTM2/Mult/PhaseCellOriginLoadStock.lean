module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginLoad
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoadStock

/-! Structural native push bound for arbitrary ordinary-header load schedules. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type}

theorem loadOriginList_native (rs : List (Fin 117 × Fin 16)) :
    mnNativePushBound 3 (loadOriginList (P₀ := P₀) (Q := Q) (A := A) (U := U) rs) := by
  induction rs with
  | nil => simp [loadOriginList,mnNativePushBound,mnActPush]
  | cons r rs ih =>
    refine ⟨?_,ih⟩
    simp [tblLoad1,bclear,toBinary,bzero,zeroBits,umulSym,scanR,keepIn,eachSym,countIter,incrField,incStep,setCarry,
      moveR,moveStep,whileR,popPush,uclear,drainR,popDo,pushN,peekR,
      mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
