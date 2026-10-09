import IntegerMultBounds.Machine.ActiveRepairEarlyFields
import IntegerMultBounds.Machine.CleanSubbank
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Actual extracted-field early repair on arbitrary caller ports. Inputs are
V/T/current controls, q/b/n and original rank; outputs are recovered T, ideal
recovered target and the actual guard flag. No packed local rank is supplied. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyFieldsPlaced
noncomputable section
open SharedPlacementAlphabet (setTape)
open CountedGuardGadgetRecord (word)
open ActiveRepairEarlyFieldsBank
variable {t : ℕ}

def ports : Fin 10 → Fin 30 := ![0,1,2,9,10,11,26,6,28,29]
theorem ports_injective : Function.Injective ports := by decide

def sources (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :=
  SharedBank.payload (before V W Z cs hs) ports

def result (caller : Tapes t 1) (focus : Fin 10 → Fin t) (q b : ℕ)
    (hb : 1≤b) (hbq : b+1≤q) (V W Z : List Bool) :=
  setTape (setTape (setTape caller (focus 7) (word (PackedInverse.w q b hb hbq V W Z)) 0)
    (focus 8) (CountedGuardGadgetFinish.key (CountedGuardGadget.flags q b Z.length V W
      (CountedGuardConstantsData.c1 q b) (CountedGuardConstantsData.c2 q b) (CountedGuardConstantsData.c3 b))) 1)
    (focus 9) (word (CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z)) 0

def program (focus : Fin 10 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed ActiveRepairEarlyFields.program (CleanSubbank.placement ports focus hf)

theorem native_clean (V W Z cs : List Bool) (hs : Fin 3 → List Bool) :
    SharedBank.strip (before V W Z cs hs) ports=SharedBank.empty 30 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [before,bank,CountedPackedInverse.bank,CountedPackedArith.bank,
    ports,Fin.exists_fin_succ]
  all_goals rfl

theorem runs (caller : Tapes t 1) (focus : Fin 10 → Fin t) (hf : Function.Injective focus)
    (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (V W Z cs : List Bool) (hs : Fin 3 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources V W Z cs hs)
    (hV : V.length=Z.length*q) (hW : W.length=Z.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedRankSplitBank.values q b Z.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program focus hf) (fun z => z=CleanSubbank.bank (s := 30) caller)
      (fun z => z=CleanSubbank.bank (s := 30) (result caller focus q b hb hbq V W Z))
      (4400*((Z.length+1)*(q+b+1))) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus q b hb hbq V W Z) _ _ _ hsrc.symm ?_ (native_clean V W Z cs hs) ?_ ?_
    (ActiveRepairEarlyFields.runs q b hb hbq hbq3 V W Z cs hs hV hW hv hc)
  · simp only [ActiveRepairEarlyFieldsCleanup.output,result,
      show (6 : Fin 30)=ports 7 from rfl,show (28 : Fin 30)=ports 8 from rfl,
      show (29 : Fin 30)=ports 9 from rfl,
      CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · simpa only [ActiveRepairEarlyFieldsCleanup.output,
      show (6 : Fin 30)=ports 7 from rfl,show (28 : Fin 30)=ports 8 from rfl,
      show (29 : Fin 30)=ports 9 from rfl,
      CompactGadgetReservationPlacement.strip_set] using native_clean V W Z cs hs
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

end
end IntegerMultBounds.Machine.ActiveRepairEarlyFieldsPlaced
