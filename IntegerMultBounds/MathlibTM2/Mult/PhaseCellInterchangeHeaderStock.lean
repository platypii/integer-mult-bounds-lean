module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyHeaders
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Native generated interchange metadata uses a fixed push allowance; erasing
its owned header list is nonincreasing. The recursive swap is handled separately. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem canonicalUnaryHeader_native (src dst a half par bits cnt saved : Fin T) :
    mnNativePushBound 2 (canonicalUnaryHeader (P := P) (Q := Q) (A := A) (U := U)
      src dst a half par bits cnt saved) := by
  simp [canonicalUnaryHeader,unaryBinary,ucopy,umulSym,scanR,keepIn,pushN,
    ldrLoop,ldrStep,ldrHalfFx,ldrBitAct,uclear,drainR,popDo,moveR,whileR,moveStep,peekR,
    mnNativePushBound,mnActPush]

theorem canonicalHeaderList_native (a half par bits cnt saved : Fin T) (rs : List (Fin T × Fin T)) :
    mnNativePushBound 2 (canonicalHeaderList (P := P) (Q := Q) (A := A) (U := U)
      a half par bits cnt saved rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih => exact ⟨canonicalUnaryHeader_native _ _ _ _ _ _ _ _,ih⟩

theorem replicaKeyHeaders_native (src dst : Fin 5 → Fin T) (a half par bits cnt saved : Fin T) :
    mnNativePushBound 2 (replicaKeyHeaders (P := P) (Q := Q) (A := A) (U := U)
      src dst a half par bits cnt saved) :=
  canonicalHeaderList_native _ _ _ _ _ _ _

theorem clearWords_native (rs : List (Fin T)) :
    mnNativePushBound 0 (clearWords (P := P) (Q := Q) (A := A) (U := U) rs) := by
  induction rs with
  | nil => exact le_refl 0
  | cons r rs ih =>
    exact ⟨by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush],ih⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
