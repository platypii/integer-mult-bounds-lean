import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedVolume

/-! The carved schedule acts directly on seven original caller descriptors and
one width descriptor. Only its three output ports change, and all forty private
workspace tapes return blank. No original descriptor is copied. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlaced
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersCarvedData
open CompactGadgetReservationHeadersCarvedSchedule
open CompactGadgetReservationHeadersWords
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t a : ℕ}

def ports : Fin 11 → Fin 40 := ![0,1,2,3,4,5,6,10,21,23,24]
theorem ports_injective : Function.Injective ports := by decide

def sources (hs : Fin 7 → List Bool) (w : ℕ) : Tapes 11 a :=
  SharedBank.payload (bank (initial hs w)) ports

def result (caller : Tapes t a) (focus : Fin 11 → Fin t)
    (s : Shape) (rows w : ℕ) (f : Front) :=
  setTape (setTape (setTape caller (focus 8)
    (RadixZeroFill.encodedBinary (bits (s.prefixRange rows f))) 1) (focus 9)
    (RadixZeroFill.encodedBinary (bits (gap s w f))) 1) (focus 10)
    (RadixZeroFill.encodedBinary (bits (suffix s w))) 1

def program (focus : Fin 11 → Fin t) (hf : Function.Injective focus) (f : Front) :=
  Placement.placed (CompactGadgetReservationHeadersCarvedSchedule.program (a := a) f)
    (CleanSubbank.placement ports focus hf)

theorem initial_clean (hs : Fin 7 → List Bool) (w : ℕ) :
    SharedBank.strip (bank (a := a) (initial hs w)) ports = SharedBank.empty 40 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [bank,CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,
    common,head,tape,initial,CompactGadgetReservationHeadersSchedule.initial,
    Tapes.append,Fin.addCases,ports,Fin.exists_fin_succ,SharedBank.empty]

theorem finished_clean (hs : Fin 7 → List Bool) (s : Shape) (n rows w : ℕ) (f : Front) :
    SharedBank.strip (bank (a := a) (finished hs s n rows w f)) ports = SharedBank.empty 40 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [bank,CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,
    common,head,tape,finished,Tapes.append,Fin.addCases,ports,Fin.exists_fin_succ,SharedBank.empty]

theorem finished_payload (hs : Fin 7 → List Bool) (s : Shape) (n rows w : ℕ) (f : Front) :
    SharedBank.payload (bank (a := a) (finished hs s n rows w f)) ports =
      result (sources hs w) id s rows w f := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [sources,SharedBank.payload,setTape,bank,
    CompactGadgetReservationHeadersCore.bank,CleanSubbank.bank,common,head,tape,
    finished,initial,CompactGadgetReservationHeadersSchedule.initial,ports,Tapes.append,Fin.addCases]

theorem constructs (caller : Tapes t a) (focus : Fin 11 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 7 → List Bool) (s : Shape) (n rows w : ℕ) (f : Front)
    (hsrc : SharedBank.payload caller focus = sources hs w)
    (hv : ∀ i, Counter.value (hs i) = originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard) (hw : w ≤ s.H) :
    HoareTime (program (a := a) focus hf f)
      (fun v => v = CleanSubbank.bank (s := 40) caller)
      (fun v => v = CleanSubbank.bank (s := 40) (result caller focus s rows w f))
      (CompactGadgetReservationHeadersOps.bound (schedule f) (initial hs w)) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus s rows w f) _ _ _ hsrc.symm ?_
    (initial_clean hs w) (finished_clean hs s n rows w f) ?_
    (CompactGadgetReservationHeadersCarvedSchedule.constructs hs s n rows w f hv hc hK hd hG hw)
  · rw [finished_payload]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,id_eq]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem constructs_volume (caller : Tapes t a) (focus : Fin 11 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 7 → List Bool) (s : Shape) (n rows w : ℕ) (f : Front)
    (hsrc : SharedBank.payload caller focus = sources hs w)
    (hv : ∀ i, Counter.value (hs i) = originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : 0 < rows) (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard)
    (hp : 0 < s.payload) (hw : w ≤ s.H) :
    HoareTime (program (a := a) focus hf f)
      (fun v => v = CleanSubbank.bank (s := 40) caller)
      (fun v => v = CleanSubbank.bank (s := 40) (result caller focus s rows w f))
      (31*CompactGadgetReservationHeadersCost.coefficient*(rows*s.recordWidth)) :=
  (constructs caller focus hf hs s n rows w f hsrc hv hc hK hd hG hw).consequence
    (fun _ h => h) (fun _ h => h)
    (CompactGadgetReservationHeadersCarvedVolume.cost_bound hs s n rows w f hv hc hr hK hd hG hp hw)

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlaced
