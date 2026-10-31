module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad
public import IntegerMultBounds.MathlibTM2.StackResources
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Narrow structural certificates for loading and retiring shared table banks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Host.SS
variable {T Q A : ℕ} {P U : Type}

theorem clearWords_native_three (rs : List (Fin T)) :
    mnNativePushBound 3 (clearWords (P := P) (Q := Q) (A := A) (U := U) rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih => exact ⟨by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush],ih⟩

private theorem chirpBankCopies_native (width savedWidth savedSource buf : Fin T)
    (rs : List (Fin T × Fin T)) :
    mnNativePushBound 3 (chirpBankCopies (P := P) (Q := Q) (A := A) (U := U)
      width savedWidth savedSource buf rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    exact ⟨by simp [padCopy,padStep,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush],ih⟩

theorem chirpBankLoad_native {n : ℕ} (rg : TblR n → Fin T)
    (source : Fin n → Fin T) (width symbols : Fin T) :
    mnNativePushBound 3 (chirpBankLoad (P := P) (Q := Q) (A := A) (U := U) rg source width symbols) := by
  unfold chirpBankLoad
  refine ⟨?_,?_,chirpBankCopies_native _ _ _ _ _⟩
  all_goals simp [ucopy,umulSym,scanR,drainR,popDo,whileR,keepIn,pushN,moveR,moveStep,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
