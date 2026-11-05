module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportBoundaryCounts
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! Count generation shares workspace proportional to its structural time bill. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type}

theorem exportFirstBoundaryCount_native (dst : Fin 117) :
    mnNativePushBound 3 (exportFirstBoundaryCount (P := P) (Q := Q) (A := A) (U := U) dst) := by
  refine ⟨?_,⟨mnNativePushBound_mono (by decide) (unaryProduct_native 26 17 dst 27 28),?_⟩⟩
  · simp [toUnary,eachSym,hornerIter,udbl,drainR,popDo,pushN,
      moveR,moveStep,whileR,peekR,popPush,mnNativePushBound,mnActPush]
  · simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

theorem exportBoundaryCount_native (last : Bool) (dst : Fin 117) :
    mnNativePushBound 3 (exportBoundaryCount (P := P) (Q := Q) (A := A) (U := U) last dst) := by
  refine ⟨preparedStandardBoundaryCounters_native last,?_,?_⟩
  · simp [moveR,moveStep,whileR,drainR,popDo,popPush,peekR,mnNativePushBound,mnActPush]
  · simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

theorem exportSlotBoundaryCount_native (slot : Fin 3) :
    mnNativePushBound 3 (exportSlotBoundaryCount (P := P) (Q := Q) (A := A) (U := U) slot) := by
  unfold exportSlotBoundaryCount
  split
  · exact exportFirstBoundaryCount_native _
  · exact exportBoundaryCount_native _ _

theorem exportBoundaryCounts_native (slots : List (Fin 3)) :
    mnNativePushBound 3
      (restoringSequence (exportSlotBoundaryCount (P := P) (Q := Q) (A := A) (U := U)) slots) := by
  induction slots with
  | nil => exact Nat.zero_le _
  | cons slot slots ih => exact ⟨exportSlotBoundaryCount_native slot,ih⟩

theorem exportBoundaryCounts_within (body : P → Pr P 117 Q A U)
    (slots : List (Fin 3)) (v v' : HS 117 Q A U) (S F : Stacks 117 A)
    (n bill depth : ℕ) (hn : n ≤ bill)
    (he : Exec body (restoringSequence exportSlotBoundaryCount slots) (mk v S) n (mk v' F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*bill) depth
      (restoringSequence exportSlotBoundaryCount slots) (mk v S) n (mk v' F) :=
  mn_native_exec_within he 3 (exportBoundaryCounts_native slots) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
