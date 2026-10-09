import IntegerMultBounds.Machine.PackedEarlyRepeatHeaders

/-! Both early repetition factors share nine actual caller ports. The two
generated words are retained for all four loads; their final erasure restores
the literal original caller, including every unselected tape and head. -/
namespace IntegerMultBounds.Machine.PackedEarlyRepeatHeadersPlaced
noncomputable section
open CompactGadgetReservationHeadersWords
open SharedPlacementAlphabet (setTape)
open PackedEarlyRepeatHeaders
variable {t a : ℕ}

def ports : Fin 9 → Fin 40 := ![0,1,2,3,4,5,6,10,14]
theorem ports_injective : Function.Injective ports := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [ports]
def inputPayload (hs : Fin 7 → List Bool) : Tapes 9 a :=
  SharedBank.payload (bank (PackedPrefixRepeatHeaders.initial hs)) ports
def outputPayload (hs : Fin 7 → List Bool) (d G n q b gap : ℕ) : Tapes 9 a :=
  SharedBank.payload (bank (finished hs d G n q b gap)) ports
def result (caller : Tapes t a) (focus : Fin 9 → Fin t) (d G n q b gap : ℕ) :=
  setTape (setTape caller (focus 7) (RadixZeroFill.encodedBinary
    (RecursiveChildQuotientsConstant.bits (beforeSource d G n q))) 1)
    (focus 8) (RadixZeroFill.encodedBinary
      (RecursiveChildQuotientsConstant.bits (PackedPrefixRepeatHeaders.repetitions d G n q b gap))) 1

theorem output_set (hs : Fin 7 → List Bool) (d G n q b gap : ℕ) :
    outputPayload (a := a) hs d G n q b gap =
      setTape (setTape (inputPayload hs) 7 (RadixZeroFill.encodedBinary
        (RecursiveChildQuotientsConstant.bits (beforeSource d G n q))) 1)
        8 (RadixZeroFill.encodedBinary
          (RecursiveChildQuotientsConstant.bits (PackedPrefixRepeatHeaders.repetitions d G n q b gap))) 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem initial_clean (hs : Fin 7 → List Bool) :
    SharedBank.strip (bank (a := a) (PackedPrefixRepeatHeaders.initial hs)) ports =
      SharedBank.empty 40 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [SharedBank.empty,ports,Fin.exists_fin_succ,
    bank,CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,Tapes.append,
    common,PackedPrefixRepeatHeaders.initial,head,tape,Fin.addCases]

theorem finished_clean (hs : Fin 7 → List Bool) (d G n q b gap : ℕ) :
    SharedBank.strip (bank (a := a) (finished hs d G n q b gap)) ports =
      SharedBank.empty 40 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [SharedBank.empty,ports,Fin.exists_fin_succ,
    bank,CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,Tapes.append,
    common,finished,head,tape,Fin.addCases]

theorem projects (caller : Tapes t a) (focus : Fin 9 → Fin t)
    (hf : Function.Injective focus) (hs : Fin 7 → List Bool) (d G n q b gap : ℕ)
    (hi : SharedBank.payload caller focus=inputPayload hs) :
    SharedBank.payload (result caller focus d G n q b gap) focus=outputPayload hs d G n q b gap := by
  rw [result,CompactGadgetReservationPlacement.payload_set _ focus hf,
    CompactGadgetReservationPlacement.payload_set caller focus hf,hi,←output_set]

theorem frames (caller : Tapes t a) (focus : Fin 9 → Fin t) (d G n q b gap : ℕ) :
    SharedBank.strip (result caller focus d G n q b gap) focus=SharedBank.strip caller focus := by
  rw [result,CompactGadgetReservationPlacement.strip_set,CompactGadgetReservationPlacement.strip_set]

def program (focus : Fin 9 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (PackedEarlyRepeatHeaders.program (a := a)) (CleanSubbank.placement ports focus hf)
def cleanupProgram (focus : Fin 9 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (PackedEarlyRepeatHeaders.cleanupProgram (a := a)) (CleanSubbank.placement ports focus hf)

theorem constructs (caller : Tapes t a) (focus : Fin 9 → Fin t)
    (hf : Function.Injective focus) (hs : Fin 7 → List Bool) (d G n q b gap rows : ℕ)
    (hv : ∀ i,Counter.value (hs i)=PackedPrefixRepeatHeaders.values d G n q b gap rows i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hG : 0<G) (hq : 0<q) (hb : 0<b) (hcap : n*q≤d*G)
    (hi : SharedBank.payload caller focus=inputPayload hs) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 40) caller)
      (fun v => v=CleanSubbank.bank (s := 40) (result caller focus d G n q b gap))
      (CompactGadgetReservationHeadersOps.bound schedule (PackedPrefixRepeatHeaders.initial hs)) := by
  apply CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus d G n q b gap) _ _ _
  · exact hi.symm
  · exact (projects caller focus hf hs d G n q b gap hi).symm
  · exact initial_clean hs
  · exact finished_clean hs d G n q b gap
  · exact (frames caller focus d G n q b gap).symm
  · exact PackedEarlyRepeatHeaders.constructs hs d G n q b gap rows hv hc hG hq hb hcap

theorem cleans (caller : Tapes t a) (focus : Fin 9 → Fin t)
    (hf : Function.Injective focus) (hs : Fin 7 → List Bool) (d G n q b gap : ℕ)
    (hi : SharedBank.payload caller focus=inputPayload hs) :
    HoareTime (cleanupProgram focus hf)
      (fun v => v=CleanSubbank.bank (s := 40) (result caller focus d G n q b gap))
      (fun v => v=CleanSubbank.bank (s := 40) caller)
      (CompactGadgetReservationHeadersOps.bound cleanup (finished hs d G n q b gap)) := by
  apply CleanSubbank.realizes _ ports focus ports_injective hf
    (result caller focus d G n q b gap) caller _ _ _
  · exact (projects caller focus hf hs d G n q b gap hi).symm
  · exact hi.symm
  · exact finished_clean hs d G n q b gap
  · exact initial_clean hs
  · exact frames caller focus d G n q b gap
  · exact PackedEarlyRepeatHeaders.cleans hs d G n q b gap

end
end IntegerMultBounds.Machine.PackedEarlyRepeatHeadersPlaced
