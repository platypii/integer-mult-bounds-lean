import IntegerMultBounds.Machine.ActivePrefixParityOnly

/-! Clean pure-parity offset production on arbitrary caller tapes, retaining every
original descriptor and spectator. All native private storage starts and ends
blank; placement adds no transitions or dimension-dependent finite control. -/
namespace IntegerMultBounds.Machine.ActivePrefixParityOnlyPlaced
noncomputable section
open ActivePrefixParityOnlyBank
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}

def ports : Fin 9 → Fin 41 := ![0,1,2,3,4,5,6,7,16]
theorem ports_injective : Function.Injective ports := by decide

def sources (hs : Fin 8 → List Bool) : Tapes 9 a :=
  (FixedHeaderBankCopy.headerBank hs).append (SharedBank.empty 1 a)
def result (caller : Tapes t a) (focus : Fin 9 → Fin t) (s : Shape) :=
  setTape caller (focus 8) (ActivePrefixOffsetStreamsCleanup.word (offsetWord s)) 0

def program (focus : Fin 9 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixParityOnly.program (a := a)) (CleanSubbank.placement ports focus hf)

theorem native_payload (hs : Fin 8 → List Bool) :
    SharedBank.payload (ActivePrefixParityOnly.input (a := a) hs) ports=sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem native_clean (hs : Fin 8 → List Bool) :
    SharedBank.strip (ActivePrefixParityOnly.input (a := a) hs) ports=SharedBank.empty 41 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [ActivePrefixParityOnly.input,ActivePrefixParityOnlyRun.bank,
    CleanSubbank.bank,Tapes.append,SharedBank.empty,base,ports,Fin.exists_fin_succ]
  all_goals rfl

theorem produces (caller : Tapes t a) (focus : Fin 9 → Fin t) (hf : Function.Injective focus)
    (s : Shape) (hs : Fin 8 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 41) caller)
      (fun v => v=CleanSubbank.bank (s := 41) (result caller focus s))
      (ActivePrefixParityOnly.constant*(2^s.W*(s.W+1))) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus s)
    _ _ _ ?_ ?_ (native_clean hs) ?_ ?_ (ActivePrefixParityOnly.runs_linear s hs hv hc)
  · rw [native_payload,hsrc]
  · have hout : ActivePrefixParityOnly.output (a := a) s hs =
        setTape (ActivePrefixParityOnly.input hs) (ports 8)
          (ActivePrefixOffsetStreamsCleanup.word (offsetWord s)) 0 := by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
    rw [hout]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,native_payload,hsrc]
  · have hout : ActivePrefixParityOnly.output (a := a) s hs =
        setTape (ActivePrefixParityOnly.input hs) (ports 8)
          (ActivePrefixOffsetStreamsCleanup.word (offsetWord s)) 0 := by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
    rw [hout,CompactGadgetReservationPlacement.strip_set]
    exact native_clean hs
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem output_word (caller : Tapes t a) (focus : Fin 9 → Fin t) (s : Shape) :
    (result caller focus s).tape (focus 8)=
      putWord (fun _ => blank) 0 ((offsetWord s).map bitSymbol) ∧
    (result caller focus s).head (focus 8)=0 := by
  simp [result,setTape,ActivePrefixOffsetStreamsCleanup.word]

theorem frame (caller : Tapes t a) (focus : Fin 9 → Fin t) (s : Shape)
    (i : Fin t) (hi : i≠focus 8) :
    (result caller focus s).tape i=caller.tape i ∧
      (result caller focus s).head i=caller.head i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.ActivePrefixParityOnlyPlaced
