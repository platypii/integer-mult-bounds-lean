module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreArchiveFromDimensions
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! Final core cropping consists only of linear counted routing and retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def normalizedCorePublicationCost (R L W N : ℕ) : ℕ :=
  packedCoreArchiveControlsCost R L W N+
    (N*(packedCoreArchiveStepCost R L (L+2*R) W+3)+2)+
    (2*(R*W+L*W+(L+2*R))+7)

def normalizedCorePublicationWorkspace (R L W N : ℕ) : ℕ :=
  13*((N+1)*(R+L+1)*(100*W+100))

theorem normalizedCorePublicationCost_le (R L W N : ℕ) :
    normalizedCorePublicationCost R L W N ≤ (N+1)*(R+L+1)*(100*W+100) := by
  unfold normalizedCorePublicationCost packedCoreArchiveControlsCost packedCoreArchiveStepCost retireCountedLineCost
  nlinarith [Nat.zero_le (N*R*W),Nat.zero_le (N*L*W),Nat.zero_le (N*W),
    Nat.zero_le (R*W),Nat.zero_le (L*W),Nat.zero_le (N*R),Nat.zero_le (N*L)]

theorem packedCoreArchiveFromDimensions_native
    (radiusHeader coreHeader replicas clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T) :
    mnNativePushBound 13 (packedCoreArchiveFromDimensions (P := P) (Q := Q) (A := A) (U := U)
      radiusHeader coreHeader replicas clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp) := by
  have hclear := mnNativePushBound_mono (by decide : 0 ≤ 13)
    (clearWords_native (P := P) (Q := Q) (A := A) (U := U) [skip,count,rows])
  simp [packedCoreArchiveFromDimensions,packedCoreArchiveControls,packedCoreArchiveLoop,countedLoop,countedLoopBody,
    packedCoreArchiveStep,copySlice,copyPrefix,copyR,Fast.copyStep,retireCountedLine,discardPrefix,
    unaryProduct,umul,umulSym,ucopy,transfer,transferAct,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,hclear,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
