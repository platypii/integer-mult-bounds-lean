import IntegerMultBounds.Machine.ActiveRepairRankFieldsField
import IntegerMultBounds.Machine.CountedRankSplitEndpoint
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Caller-shared rank-field extraction on the real scan counter. Nine blank
private slots are reused by all field copies and subsequent source selection;
the five-tape field machine uses just its one clock slot within that bank. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankFieldsPlaced
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

def localBank (f g : ℤ → Fin 5) (hs : Fin 2 → List Bool) :=
  (ActiveRepairRankFieldsField.bank f g 1 0 hs).append (SharedBank.empty 4 1)
def ports : Fin 4 → Fin 9 := ![0,1,2,3]
theorem ports_injective : Function.Injective ports := by decide

def sources (cs : List Bool) (g : ℤ → Fin 5) (hs : Fin 2 → List Bool) :=
  SharedBank.payload (localBank (RepairScan.ctrTape cs) g hs) ports

def program (focus : Fin 4 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (extend (ActiveRepairRankFieldsField.program (a := 1)) 4)
    (CleanSubbank.placement ports focus hf)

def result (caller : Tapes t 1) (focus : Fin 4 → Fin t) (g : ℤ → Fin 5)
    (cs : List Bool) (start width : ℕ) :=
  setTape caller (focus 1) (putWord g 0 ((Gather.field cs start width).map bitSymbol)) 0

theorem local_clean (f g : ℤ → Fin 5) (hs : Fin 2 → List Bool) :
    SharedBank.strip (localBank f g hs) ports=SharedBank.empty 9 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [localBank,ports,ActiveRepairRankFieldsField.bank,SharedBank.empty,
    Tapes.append,Fin.addCases,Fin.exists_fin_succ]

theorem local_output (f g : ℤ → Fin 5) (hs : Fin 2 → List Bool) (cs : List Bool) (start width : ℕ) :
    localBank f (putWord g 0 ((Gather.field cs start width).map bitSymbol)) hs=
      setTape (localBank f g hs) (ports 1) (putWord g 0 ((Gather.field cs start width).map bitSymbol)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (caller : Tapes t 1) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (g : ℤ → Fin 5) (cs : List Bool) (hs : Fin 2 → List Bool) (start width : ℕ)
    (hsrc : SharedBank.payload caller focus=sources cs g hs)
    (hv0 : Counter.value (hs 0)=start) (hv1 : Counter.value (hs 1)=width) :
    HoareTime (program focus hf)
      (fun v => v=CleanSubbank.bank (s := 9) caller)
      (fun v => v=CleanSubbank.bank (s := 9) (result caller focus g cs start width))
      (ActiveRepairRankFieldsField.cost start width hs) := by
  have h := ActiveRepairRankFieldsField.runs CountedRankSplitEndpoint.counterBase g 0 cs hs start width hv0 hv1
    (CountedRankSplitEndpoint.counter_tail cs)
  rw [←CountedRankSplitEndpoint.counter_word cs] at h
  have hh := hoare_extend_eq h (SharedBank.empty 4 1)
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus g cs start width) _ _ _ hsrc.symm ?_
    (local_clean _ _ _) (local_clean _ _ _) ?_ hh
  · rw [local_output]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem runs_linear (caller : Tapes t 1) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (g : ℤ → Fin 5) (cs : List Bool) (hs : Fin 2 → List Bool) (start width : ℕ)
    (hsrc : SharedBank.payload caller focus=sources cs g hs)
    (hv0 : Counter.value (hs 0)=start) (hv1 : Counter.value (hs 1)=width)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program focus hf)
      (fun v => v=CleanSubbank.bank (s := 9) caller)
      (fun v => v=CleanSubbank.bank (s := 9) (result caller focus g cs start width))
      (200*(start+width+1)) :=
  (runs caller focus hf g cs hs start width hsrc hv0 hv1).consequence
    (fun _ h => h) (fun _ h => h) (ActiveRepairRankFieldsField.cost_linear start width hs hv0 hv1 hc)

end
end IntegerMultBounds.Machine.ActiveRepairRankFieldsPlaced
