import IntegerMultBounds.Machine.ActivePrefixDirtyControl

/-! Clean selected/control/parity-XOR offset production on arbitrary caller tapes, retaining every
original descriptor and spectator. All native private storage starts and ends
blank; placement adds no transitions or dimension-dependent finite control. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlPlaced
noncomputable section
open ActivePrefixDirtyControlData
open SharedPlacementAlphabet (setTape)
open BinaryVaryingOffsetGatherPlaced (Kind)
variable {a t : ℕ} {k : Kind}

def ports : Fin 7 → Fin 39 := ![0,1,2,3,4,5,14]
theorem ports_injective : Function.Injective ports := by decide

def sources (hs : Fin 6 → List Bool) : Tapes 7 a :=
  (FixedHeaderBankCopy.headerBank hs).append (SharedBank.empty 1 a)
def result (caller : Tapes t a) (focus : Fin 7 → Fin t) (s : Shape k) :=
  setTape caller (focus 6) (ActivePrefixOffsetStreamsCleanup.word (offsetWord s)) 0

def program (k : Kind) (focus : Fin 7 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixDirtyControl.program (a := a) k) (CleanSubbank.placement ports focus hf)

theorem native_payload (hs : Fin 6 → List Bool) :
    SharedBank.payload (ActivePrefixDirtyControl.input (a := a) hs) ports=sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem native_clean (hs : Fin 6 → List Bool) :
    SharedBank.strip (ActivePrefixDirtyControl.input (a := a) hs) ports=SharedBank.empty 39 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [ActivePrefixDirtyControl.input,ActivePrefixDirtyControlHeaders.bank,
    CleanSubbank.bank,Tapes.append,SharedBank.empty,base,ports,Fin.exists_fin_succ]
  all_goals rfl

theorem produces (caller : Tapes t a) (focus : Fin 7 → Fin t) (hf : Function.Injective focus)
    (s : Shape k) (hs : Fin 6 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program k focus hf) (fun v => v=CleanSubbank.bank (s := 39) caller)
      (fun v => v=CleanSubbank.bank (s := 39) (result caller focus s))
      (ActivePrefixDirtyControl.constant*ActivePrefixDirtyControl.volume s) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus s)
    _ _ _ ?_ ?_ (native_clean hs) ?_ ?_ (ActivePrefixDirtyControl.runs_linear s hs hv hc)
  · rw [native_payload,hsrc]
  · have hout : ActivePrefixDirtyControl.output (a := a) s hs =
        setTape (ActivePrefixDirtyControl.input hs) (ports 6)
          (ActivePrefixOffsetStreamsCleanup.word (offsetWord s)) 0 := by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
    rw [hout]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,native_payload,hsrc]
  · have hout : ActivePrefixDirtyControl.output (a := a) s hs =
        setTape (ActivePrefixDirtyControl.input hs) (ports 6)
          (ActivePrefixOffsetStreamsCleanup.word (offsetWord s)) 0 := by
      apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
    rw [hout,CompactGadgetReservationPlacement.strip_set]
    exact native_clean hs
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem frame (caller : Tapes t a) (focus : Fin 7 → Fin t) (s : Shape k)
    (i : Fin t) (hi : i≠focus 6) :
    (result caller focus s).tape i=caller.tape i ∧
      (result caller focus s).head i=caller.head i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlPlaced
