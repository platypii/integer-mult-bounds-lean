import IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrection

/-! Arbitrary-caller correction wrapper. Six original descriptors are retained,
only the output changes, and all fifty native working tapes are blank again. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionPlaced
noncomputable section
open ActivePrefixDirtyControlData (Shape values)
open ActivePrefixDirtyControlCorrectionBank
open ActivePrefixDirtyControlCorrectionRun (bank)
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}

def ports : Fin 7 → Fin 50 := ![0,1,2,3,4,5,8]
theorem ports_injective : Function.Injective ports := by decide

def sources (hs : Fin 6 → List Bool) : Tapes 7 a := ActivePrefixDirtyControlPlaced.sources hs
def result (caller : Tapes t a) (focus : Fin 7 → Fin t) (s : Shape .selected) :=
  setTape caller (focus 6) (ActivePrefixCorrectionOffsetSubtract.word (ActivePrefixDirtyControlCorrectionData.word s)) 0

def program (focus : Fin 7 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixDirtyControlCorrectionRun.program (a := a)) (CleanSubbank.placement ports focus hf)

theorem native_payload (hs : Fin 6 → List Bool) :
    SharedBank.payload (bank (base (a := a) hs)) ports=sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem native_clean (hs : Fin 6 → List Bool) :
    SharedBank.strip (bank (base (a := a) hs)) ports=SharedBank.empty 50 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [bank,CleanSubbank.bank,Tapes.append,SharedBank.empty,base,ports,Fin.exists_fin_succ]
  all_goals rfl

theorem native_output (s : Shape .selected) (hs : Fin 6 → List Bool) :
    bank (output (a := a) s hs)=result (bank (base hs)) ports s := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem produces (caller : Tapes t a) (focus : Fin 7 → Fin t) (hf : Function.Injective focus)
    (s : Shape .selected) (hs : Fin 6 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 50) caller)
      (fun v => v=CleanSubbank.bank (s := 50) (result caller focus s))
      (ActivePrefixDirtyControlCorrection.constant*ActivePrefixDirtyControl.volume s) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus s)
    _ _ _ ?_ ?_ (native_clean hs) ?_ ?_ (ActivePrefixDirtyControlCorrection.runs_linear s hs hv hc)
  · rw [native_payload,hsrc]
  · rw [native_output]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,native_payload,hsrc]
  · rw [native_output]
    simp only [result,CompactGadgetReservationPlacement.strip_set,native_clean]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem frame (caller : Tapes t a) (focus : Fin 7 → Fin t) (s : Shape .selected)
    (i : Fin t) (hi : i≠focus 6) :
    (result caller focus s).tape i=caller.tape i ∧ (result caller focus s).head i=caller.head i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionPlaced
