import IntegerMultBounds.Machine.ActivePrefixDirtyControlRun
import IntegerMultBounds.Machine.BinaryVaryingParityOnlyPlaced

/-! Exact caller endpoints for the dirty-U controlled physical gather. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlPureBank
noncomputable section
open ActivePrefixDirtyControlData hiding offsetWord gathered offset_length
open BinaryVaryingOffsetGatherPlaced (Kind sourceWidth outputWidth)
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}

def offsetWord (s : Shape .parity) := BinaryVaryingParityOnlyGather.word s.q s.b s.hb s.hbq (tempWord s) (controlWord s)
def gathered (s : Shape .parity) (hs : Fin 6 → List Bool) :=
  BinaryVaryingParityOnlyPlaced.result (controlReady (a := a) s hs) gatherFocus
    s.q s.b s.hb s.hbq (tempWord s) (controlWord s) 0 0 0
@[simp] theorem offset_length (s : Shape .parity) : (offsetWord s).length=2^s.W*outputRowWidth s := by
  simp [offsetWord,outputRowWidth,outputWidth,Nat.mul_assoc]

def emitted (s : Shape .parity) (hs : Fin 6 → List Bool) :=
  setTape (setTape (setTape (controlReady (a := a) s hs) (gatherFocus 3)
    ((controlReady s hs).tape (gatherFocus 3)) (0+(controlWord s).length*sourceWidth .parity s.q s.b))
    (gatherFocus 4) ((controlReady s hs).tape (gatherFocus 4)) (0+(controlWord s).length))
    (gatherFocus 5) (putWord ((controlReady s hs).tape (gatherFocus 5)) 0 ((offsetWord s).map bitSymbol))
    (0+(controlWord s).length*outputWidth .parity s.q s.b)

theorem gathered_eq (s : Shape .parity) (hs : Fin 6 → List Bool) : gathered (a := a) s hs=emitted s hs := by
  have hl := BinaryVaryingParityOnlyPlaced.result_payload (controlReady (a := a) s hs)
    gatherFocus (by decide) s.q s.b s.hb s.hbq (tempWord s) (controlWord s) 0 0 0
  change SharedBank.payload (gathered (a := a) s hs) gatherFocus=_ at hl
  have hr : SharedBank.payload (emitted (a := a) s hs) gatherFocus=
      BinaryVaryingParityOnlyPlaced.after (SharedBank.payload (controlReady s hs) gatherFocus)
        s.q s.b s.hb s.hbq (tempWord s) (controlWord s) 0 0 0 := by
    unfold emitted
    rw [CompactGadgetReservationPlacement.payload_set _ _ (by decide : Function.Injective gatherFocus),
      CompactGadgetReservationPlacement.payload_set _ _ (by decide : Function.Injective gatherFocus),
      CompactGadgetReservationPlacement.payload_set _ _ (by decide : Function.Injective gatherFocus)]
    rfl
  have hsl : SharedBank.strip (gathered (a := a) s hs) gatherFocus=SharedBank.strip (controlReady s hs) gatherFocus :=
    (BinaryVaryingOffsetGatherPlaced.installed_frame (controlReady s hs) gatherFocus _).symm
  have hsr : SharedBank.strip (emitted (a := a) s hs) gatherFocus=SharedBank.strip (controlReady s hs) gatherFocus := by
    simp only [emitted,CompactGadgetReservationPlacement.strip_set]
  have h : SharedBank.bank (gathered (a := a) s hs) gatherFocus=SharedBank.bank (emitted s hs) gatherFocus := by
    unfold SharedBank.bank
    rw [hl,hr,hsl,hsr]
  simpa only [SharedBank.active_bank] using congrArg (Placement.active (SharedBank.placement gatherFocus)) h

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlPureBank
