import IntegerMultBounds.Machine.ActivePrefixOffsetRepeatAlphabet
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Physically repeat a generated offset word for an arbitrary caller row
count. The three caller ports are rows/base/output; four private tapes are
returned blank, and the original descriptor, base and spectators are retained. -/
namespace IntegerMultBounds.Machine.ActivePrefixOffsetRepeatPlaced
noncomputable section
open ActivePrefixOffsetRepeatAlphabet (word bank)
open BinaryAddressOffsetRepeatData (copies)
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

def ports : Fin 3 → Fin 4 := ![3,0,1]
theorem ports_injective : Function.Injective ports := by decide

def sources (xs rs : List Bool) : Tapes 3 a :=
  SharedBank.payload (bank xs rs (fun _ => blank)) ports

theorem sources_eq (xs rs : List Bool) : sources (a := a) xs rs=
    ⟨![1,0,0],![RadixZeroFill.encodedBinary rs,word xs,fun _ => blank]⟩ := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def result (caller : Tapes t a) (focus : Fin 3 → Fin t) (xs : List Bool) (rows : ℕ) :=
  setTape caller (focus 2) (word (copies xs rows)) 0

def program (focus : Fin 3 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixOffsetRepeatAlphabet.program a) (CleanSubbank.placement ports focus hf)

theorem clean (xs rs : List Bool) :
    SharedBank.strip (bank (a := a) xs rs (fun _ => blank)) ports=SharedBank.empty 4 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [bank,ports,Fin.exists_fin_succ]

theorem repeats (caller : Tapes t a) (focus : Fin 3 → Fin t) (hf : Function.Injective focus)
    (xs rs : List Bool) (rows : ℕ)
    (hsrc : SharedBank.payload caller focus=sources xs rs)
    (hv : Counter.value rs=rows) (hc : GrowingCounterData.Canonical rs) :
    HoareTime (program (a := a) focus hf)
      (fun v => v=CleanSubbank.bank (s := 4) caller)
      (fun v => v=CleanSubbank.bank (s := 4) (result caller focus xs rows))
      (54*(rows*xs.length+1)) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus xs rows) _ _ _ hsrc.symm ?_ (clean xs rs) ?_ ?_
    (ActivePrefixOffsetRepeatAlphabet.repeats xs rs rows hv hc)
  · rw [ActivePrefixOffsetRepeatAlphabet.output_eq]
    change SharedBank.payload (setTape (bank xs rs (fun _ => blank)) (ports 2)
      (word (copies xs rows)) 0) ports = SharedBank.payload (result caller focus xs rows) focus
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · rw [ActivePrefixOffsetRepeatAlphabet.output_eq]
    change SharedBank.strip (setTape (bank xs rs (fun _ => blank)) (ports 2)
      (word (copies xs rows)) 0) ports = SharedBank.empty 4 a
    rw [CompactGadgetReservationPlacement.strip_set]
    exact clean xs rs
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem output_word (caller : Tapes t a) (focus : Fin 3 → Fin t) (xs : List Bool) (rows : ℕ) :
    (result caller focus xs rows).tape (focus 2)=
      putWord (fun _ => blank) 0 (((List.replicate rows xs).flatten).map bitSymbol) ∧
    (result caller focus xs rows).head (focus 2)=0 := by
  simp [result,setTape,word,ActivePrefixOffsetRepeatRun.copies_replicate]

theorem frame (caller : Tapes t a) (focus : Fin 3 → Fin t) (xs : List Bool) (rows : ℕ)
    (i : Fin t) (hi : i≠focus 2) :
    (result caller focus xs rows).tape i=caller.tape i ∧
    (result caller focus xs rows).head i=caller.head i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.ActivePrefixOffsetRepeatPlaced
