import IntegerMultBounds.Machine.ActivePrefixCorrectionOffset

/-! Caller-placed complete correction producer. Only the eight original
headers are inputs; the correction output starts blank. All private tapes
return blank, original headers and spectators retain their exact positions. -/
namespace IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetPlaced
noncomputable section
open ActivePrefixSelectedOffsetBank (Shape values)
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}

def ports : Fin 9 → Fin 57 := ![0,1,2,3,4,5,6,7,10]
theorem ports_injective : Function.Injective ports := by decide

def sources (hs : Fin 8 → List Bool) : Tapes 9 a :=
  (FixedHeaderBankCopy.headerBank hs).append (SharedBank.empty 1 a)
def result (caller : Tapes t a) (focus : Fin 9 → Fin t) (s : Shape) :=
  setTape caller (focus 8) (ActivePrefixCorrectionOffsetSubtract.word (ActivePrefixCorrectionOffsetData.word s)) 0

def program (focus : Fin 9 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixCorrectionOffset.program (a := a)) (CleanSubbank.placement ports focus hf)

theorem native_payload (hs : Fin 8 → List Bool) :
    SharedBank.payload (ActivePrefixCorrectionOffset.input (a := a) hs) ports=sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem native_clean (hs : Fin 8 → List Bool) :
    SharedBank.strip (ActivePrefixCorrectionOffset.input (a := a) hs) ports=SharedBank.empty 57 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [ActivePrefixCorrectionOffset.input,ActivePrefixCorrectionOffsetRun.bank,
    CleanSubbank.bank,Tapes.append,SharedBank.empty,ActivePrefixCorrectionOffsetBank.base,ports,Fin.exists_fin_succ]
  all_goals rfl

theorem native_output (s : Shape) (hs : Fin 8 → List Bool) :
    ActivePrefixCorrectionOffset.output (a := a) s hs=
      setTape (ActivePrefixCorrectionOffset.input hs) (ports 8)
        (ActivePrefixCorrectionOffsetSubtract.word (ActivePrefixCorrectionOffsetData.word s)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem produces (caller : Tapes t a) (focus : Fin 9 → Fin t) (hf : Function.Injective focus)
    (s : Shape) (hs : Fin 8 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 57) caller)
      (fun v => v=CleanSubbank.bank (s := 57) (result caller focus s))
      (ActivePrefixCorrectionOffset.constant*(2^s.W*(s.W+1))) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus s)
    _ _ _ ?_ ?_ (native_clean hs) ?_ ?_ (ActivePrefixCorrectionOffset.runs_linear s hs hv hc)
  · rw [native_payload,hsrc]
  · rw [native_output]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,native_payload,hsrc]
  · rw [native_output,CompactGadgetReservationPlacement.strip_set]
    exact native_clean hs
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem output_word (caller : Tapes t a) (focus : Fin 9 → Fin t) (s : Shape) :
    (result caller focus s).tape (focus 8)=
      putWord (fun _ => blank) 0 ((ActivePrefixCorrectionOffsetData.word s).map bitSymbol) ∧
    (result caller focus s).head (focus 8)=0 := by
  simp [result,setTape,ActivePrefixCorrectionOffsetSubtract.word]

theorem frame (caller : Tapes t a) (focus : Fin 9 → Fin t) (s : Shape)
    (i : Fin t) (hi : i≠focus 8) :
    (result caller focus s).tape i=caller.tape i ∧
      (result caller focus s).head i=caller.head i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetPlaced
