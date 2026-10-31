module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkDimensionBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Dimension-bank allocation is linear native work; release has no pushes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem unaryProduct_native (a b dst tmp saved : Fin T) :
    mnNativePushBound 2 (unaryProduct (P := P) (Q := Q) (A := A) (U := U) a b dst tmp saved) := by
  simp [unaryProduct,scanP,popPush,drainR,popDo,ucopy,umulSym,scanR,keepIn,pushN,
    moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]

theorem unaryPowerChain_native (base src tmp saved : Fin T) (ds : List (Fin T)) :
    mnNativePushBound 2 (unaryPowerChain (P := P) (Q := Q) (A := A) (U := U) base src tmp saved ds) := by
  induction ds generalizing src with
  | nil => exact Nat.zero_le _
  | cons dst ds ih => exact ⟨unaryProduct_native _ _ _ _ _,ih dst⟩

theorem chunkDimensionBank_native (base one width tmp saved : Fin T) (ps bs : List (Fin T)) :
    mnNativePushBound 2 (chunkDimensionBank (P := P) (Q := Q) (A := A) (U := U)
      base one width tmp saved ps bs) :=
  ⟨unaryPowerChain_native _ _ _ _ _,unaryPowerChain_native _ _ _ _ _⟩

theorem releaseChunkDimensionBank_native (ps bs : List (Fin T)) :
    mnNativePushBound 0 (releaseChunkDimensionBank (P := P) (Q := Q) (A := A) (U := U) ps bs) :=
  ⟨clearWords_native bs,clearWords_native ps⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
