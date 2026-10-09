import IntegerMultBounds.Machine.ActivePrefixDirtyControlHeaders

/-! Exact caller endpoints for the dirty-U controlled physical gather. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlBank
noncomputable section
open ActivePrefixDirtyControlData
open BinaryVaryingOffsetGatherPlaced (Kind sourceWidth outputWidth)
open SharedPlacementAlphabet (setTape)
variable {a : ℕ} {k : Kind}

theorem gather_tapes (s : Shape k) (hs : Fin 6 → List Bool) :
    (∀ i : Fin 3, (controlReady (a := a) s hs).tape (gatherFocus ⟨i.val,by omega⟩)=
      RadixZeroFill.encodedBinary (gatherHeaders s hs i)) ∧
    (controlReady (a := a) s hs).tape (gatherFocus 3)=putWord (fun _ => blank) 0 ((tempWord s).map bitSymbol) ∧
    (controlReady (a := a) s hs).tape (gatherFocus 4)=putWord (fun _ => blank) 0 ((controlWord s).map bitSymbol) := by
  cases k <;> refine ⟨?_,rfl,rfl⟩ <;> intro i <;> fin_cases i <;> rfl

theorem gather_heads (s : Shape k) (hs : Fin 6 → List Bool) :
    (∀ i : Fin 3, (controlReady (a := a) s hs).head (gatherFocus ⟨i.val,by omega⟩)=1) ∧
    (controlReady (a := a) s hs).head (gatherFocus 3)=0 ∧
    (controlReady (a := a) s hs).head (gatherFocus 4)=0 ∧
    (controlReady (a := a) s hs).head (gatherFocus 5)=0 := by
  cases k <;> refine ⟨?_,rfl,rfl,rfl⟩ <;> intro i <;> fin_cases i <;> rfl

def emitted (s : Shape k) (hs : Fin 6 → List Bool) :=
  setTape (setTape (setTape (controlReady (a := a) s hs) (gatherFocus 3)
    ((controlReady s hs).tape (gatherFocus 3)) (0+(controlWord s).length*sourceWidth k s.q s.b))
    (gatherFocus 4) ((controlReady s hs).tape (gatherFocus 4)) (0+(controlWord s).length))
    (gatherFocus 5) (putWord ((controlReady s hs).tape (gatherFocus 5)) 0 ((offsetWord s).map bitSymbol))
    (0+(controlWord s).length*outputWidth k s.q s.b)

theorem gathered_eq (s : Shape k) (hs : Fin 6 → List Bool) : gathered (a := a) s hs=emitted s hs := by
  have hl := BinaryVaryingOffsetGatherPlaced.result_payload k (controlReady (a := a) s hs)
    gatherFocus (by decide) s.q s.b s.hb s.hbq (tempWord s) (controlWord s) 0 0 0
  change SharedBank.payload (gathered (a := a) s hs) gatherFocus=_ at hl
  have hr : SharedBank.payload (emitted (a := a) s hs) gatherFocus=
      BinaryVaryingOffsetGatherPlaced.after k (SharedBank.payload (controlReady s hs) gatherFocus)
        s.q s.b s.hb s.hbq (tempWord s) (controlWord s) 0 0 0 := by
    unfold emitted
    rw [CompactGadgetReservationPlacement.payload_set _ _ (by decide : Function.Injective gatherFocus),
      CompactGadgetReservationPlacement.payload_set _ _ (by decide : Function.Injective gatherFocus),
      CompactGadgetReservationPlacement.payload_set _ _ (by decide : Function.Injective gatherFocus)]
    cases k
    · rfl
    · simp only [sourceWidth,Nat.cast_one,mul_one]
      rfl
    · rfl
  have hsl : SharedBank.strip (gathered (a := a) s hs) gatherFocus=SharedBank.strip (controlReady s hs) gatherFocus :=
    (BinaryVaryingOffsetGatherPlaced.installed_frame (controlReady s hs) gatherFocus _).symm
  have hsr : SharedBank.strip (emitted (a := a) s hs) gatherFocus=SharedBank.strip (controlReady s hs) gatherFocus := by
    simp only [emitted,CompactGadgetReservationPlacement.strip_set]
  have h : SharedBank.bank (gathered (a := a) s hs) gatherFocus=SharedBank.bank (emitted s hs) gatherFocus := by
    unfold SharedBank.bank
    rw [hl,hr,hsl,hsr]
  simpa only [SharedBank.active_bank] using congrArg (Placement.active (SharedBank.placement gatherFocus)) h

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlBank
