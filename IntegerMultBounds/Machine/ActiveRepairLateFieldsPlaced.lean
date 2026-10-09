import IntegerMultBounds.Machine.ActiveRepairLateFields
import IntegerMultBounds.Machine.CleanSubbank
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Clean placement of the actual later extracted-field computation. Original
fields, current controls, headers and full rank are retained; only recovered
destination fields and guard flag are installed in the caller. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateFieldsPlaced
noncomputable section
open SharedPlacementAlphabet (setTape)
open CountedGuardGadgetRecord (word)
open ActiveRepairLateFieldsBank
variable {t : ℕ}

def ports : Fin 12 → Fin 35 := ![31,32,33,3,11,12,13,34,1,2,28,30]
theorem ports_injective : Function.Injective ports := by decide

def sources (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :=
  SharedBank.payload (before V W U X cs hs) ports

def result (caller : Tapes t 1) (focus : Fin 12 → Fin t) (q b : ℕ)
    (hb : 1≤b) (hbq : b+1≤q) (V W U X : List Bool) :=
  setTape (setTape (setTape (setTape caller (focus 8)
    (word (CountedLateRepairInverse.temp q b hb hbq V W U X)) 0) (focus 9)
    (word (CountedLateRepairInverse.restored b hb U X)) 0) (focus 10)
    (CountedLateRepairFlag.key (CountedLateRepairGuard.flag q b V W X ||
      CountedLateRepairGuard.flag q b V U X)) 1) (focus 11)
    (word (CountedIdealToggle.word q (CountedLateRepairInverse.target q b hb hbq V W U X) X)) 0

def program (focus : Fin 12 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed ActiveRepairLateFields.program (CleanSubbank.placement ports focus hf)

theorem native_clean (V W U X cs : List Bool) (hs : Fin 3 → List Bool) :
    SharedBank.strip (before V W U X cs hs) ports=SharedBank.empty 35 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [before,bank,CountedLateRepairGuard.before,CountedLateRepairGuard.bank,
    originals,ports,Fin.exists_fin_succ]
  all_goals rfl

theorem runs (caller : Tapes t 1) (focus : Fin 12 → Fin t) (hf : Function.Injective focus)
    (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hbq3 : b+3≤q)
    (V W U X cs : List Bool) (hs : Fin 3 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources V W U X cs hs)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program focus hf) (fun z => z=CleanSubbank.bank (s := 35) caller)
      (fun z => z=CleanSubbank.bank (s := 35) (result caller focus q b hb hbq V W U X))
      (9700*((X.length+1)*(q+b+1))) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus q b hb hbq V W U X) _ _ _ hsrc.symm ?_ (native_clean V W U X cs hs) ?_ ?_
    (ActiveRepairLateFields.runs q b hb hbq hbq3 V W U X cs hs hV hW hU hv hc)
  · simp only [ActiveRepairLateFieldsCleanup.output_eq,result,
      show (1 : Fin 35)=ports 8 from rfl,show (2 : Fin 35)=ports 9 from rfl,
      show (28 : Fin 35)=ports 10 from rfl,show (30 : Fin 35)=ports 11 from rfl,
      CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · simpa only [ActiveRepairLateFieldsCleanup.output_eq,
      show (1 : Fin 35)=ports 8 from rfl,show (2 : Fin 35)=ports 9 from rfl,
      show (28 : Fin 35)=ports 10 from rfl,show (30 : Fin 35)=ports 11 from rfl,
      CompactGadgetReservationPlacement.strip_set] using native_clean V W U X cs hs
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

end
end IntegerMultBounds.Machine.ActiveRepairLateFieldsPlaced
