import IntegerMultBounds.Machine.PackedPrefixRepeatHeaders

/-! The paid prefix repetition factors on eight arbitrary caller ports.
Seven original descriptors are retained; the eighth receives the constructed
factor L. The actual erasure restores the original caller and all workspace. -/
namespace IntegerMultBounds.Machine.PackedPrefixRepeatHeadersPlaced
noncomputable section
open CompactGadgetReservationHeadersWords
open SharedPlacementAlphabet (setTape)
open PackedPrefixRepeatHeaders
variable {t a : ℕ}

def ports : Fin 8 → Fin 40 := ![0,1,2,3,4,5,6,14]
theorem ports_injective : Function.Injective ports := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ports]

def inputPayload (hs : Fin 7 → List Bool) : Tapes 8 a :=
  SharedBank.payload (bank (initial hs)) ports
def outputPayload (hs : Fin 7 → List Bool) (d G n q b gap : ℕ) : Tapes 8 a :=
  SharedBank.payload (bank (finished hs d G n q b gap)) ports

theorem output_set (hs : Fin 7 → List Bool) (d G n q b gap : ℕ) :
    outputPayload (a := a) hs d G n q b gap =
      setTape (inputPayload hs) 7 (RadixZeroFill.encodedBinary
        (RecursiveChildQuotientsConstant.bits (repetitions d G n q b gap))) 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem initial_clean (hs : Fin 7 → List Bool) :
    SharedBank.strip (bank (a := a) (initial hs)) ports = SharedBank.empty 40 a := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals fin_cases i
  all_goals simp [SharedBank.empty,ports,Fin.exists_fin_succ,
    bank,CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,Tapes.append,
    common,initial,head,tape,Fin.addCases]

theorem finished_clean (hs : Fin 7 → List Bool) (d G n q b gap : ℕ) :
    SharedBank.strip (bank (a := a) (finished hs d G n q b gap)) ports =
      SharedBank.empty 40 a := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals fin_cases i
  all_goals simp [SharedBank.empty,ports,Fin.exists_fin_succ,
    bank,CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,Tapes.append,
    common,finished,head,tape,Fin.addCases]

def program (focus : Fin 8 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (PackedPrefixRepeatHeaders.program (a := a))
    (CleanSubbank.placement ports focus hf)
def cleanupProgram (focus : Fin 8 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (PackedPrefixRepeatHeaders.cleanupProgram (a := a))
    (CleanSubbank.placement ports focus hf)
def result (caller : Tapes t a) (focus : Fin 8 → Fin t) (d G n q b gap : ℕ) :=
  setTape caller (focus 7) (RadixZeroFill.encodedBinary
    (RecursiveChildQuotientsConstant.bits (repetitions d G n q b gap))) 1

theorem constructs (caller : Tapes t a) (focus : Fin 8 → Fin t)
    (hf : Function.Injective focus) (hs : Fin 7 → List Bool) (d G n q b gap rows : ℕ)
    (hv : ∀ i,Counter.value (hs i)=values d G n q b gap rows i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hG : 0<G) (hq : 0<q) (hb : 0<b) (hcap : n*q≤d*G)
    (hi : SharedBank.payload caller focus=inputPayload hs) :
    HoareTime (program focus hf)
      (fun v => v=CleanSubbank.bank (s := 40) caller)
      (fun v => v=CleanSubbank.bank (s := 40) (result caller focus d G n q b gap))
      (CompactGadgetReservationHeadersOps.bound schedule (initial hs)) := by
  apply CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus d G n q b gap) _ _ _
  · exact hi.symm
  · rw [result,CompactGadgetReservationPlacement.payload_set caller focus hf,hi,←output_set]
    rfl
  · exact initial_clean hs
  · exact finished_clean hs d G n q b gap
  · exact (CompactGadgetReservationPlacement.strip_set caller focus 7 _ 1).symm
  · exact PackedPrefixRepeatHeaders.constructs hs d G n q b gap rows hv hc hG hq hb hcap

theorem cleans (caller : Tapes t a) (focus : Fin 8 → Fin t)
    (hf : Function.Injective focus) (hs : Fin 7 → List Bool) (d G n q b gap : ℕ)
    (hi : SharedBank.payload caller focus=inputPayload hs) :
    HoareTime (cleanupProgram focus hf)
      (fun v => v=CleanSubbank.bank (s := 40) (result caller focus d G n q b gap))
      (fun v => v=CleanSubbank.bank (s := 40) caller)
      (2*(RecursiveChildQuotientsConstant.bits (repetitions d G n q b gap)).length+4) := by
  apply CleanSubbank.realizes _ ports focus ports_injective hf
    (result caller focus d G n q b gap) caller _ _ _
  · rw [result,CompactGadgetReservationPlacement.payload_set caller focus hf,hi,←output_set]
    rfl
  · exact hi.symm
  · exact finished_clean hs d G n q b gap
  · exact initial_clean hs
  · exact CompactGadgetReservationPlacement.strip_set caller focus 7 _ 1
  · exact PackedPrefixRepeatHeaders.cleans hs d G n q b gap

end
end IntegerMultBounds.Machine.PackedPrefixRepeatHeadersPlaced
