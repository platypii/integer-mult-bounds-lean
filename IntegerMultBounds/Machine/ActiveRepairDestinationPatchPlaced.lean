import IntegerMultBounds.Machine.ActiveRepairDestinationPatchOverwrite
import IntegerMultBounds.Machine.CountedRankSplitEndpoint
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Runtime replacement writes on caller-selected tapes, sharing nine blank
private slots with field parsing and preserving the replacement word and headers. -/
namespace IntegerMultBounds.Machine.ActiveRepairDestinationPatchPlaced
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

def localBank (f g : ℤ → Fin 5) (hs : Fin 2 → List Bool) :=
  (ActiveRepairRankFieldsField.bank f g 0 0 hs).append (SharedBank.empty 4 1)
def ports : Fin 4 → Fin 9 := ![0,1,2,3]
theorem ports_injective : Function.Injective ports := by decide

def sources (cs : List Bool) (g : ℤ → Fin 5) (hs : Fin 2 → List Bool) :=
  SharedBank.payload (localBank (putWord (fun _ => blank) 0 (cs.map bitSymbol)) g hs) ports

def program (focus : Fin 4 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (extend (ActiveRepairDestinationPatchOverwrite.program (a := 1)) 4)
    (CleanSubbank.placement ports focus hf)

def result (caller : Tapes t 1) (focus : Fin 4 → Fin t) (g : ℤ → Fin 5)
    (cs : List Bool) (start : ℕ) :=
  setTape caller (focus 1) (putWord g start (cs.map bitSymbol)) 0

theorem local_clean (f g : ℤ → Fin 5) (hs : Fin 2 → List Bool) :
    SharedBank.strip (localBank f g hs) ports=SharedBank.empty 9 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [localBank,ports,ActiveRepairRankFieldsField.bank,SharedBank.empty,
    Tapes.append,Fin.addCases,Fin.exists_fin_succ]

theorem local_output (f g : ℤ → Fin 5) (hs : Fin 2 → List Bool) (cs : List Bool) (start : ℕ) :
    localBank f (putWord g start (cs.map bitSymbol)) hs=
      setTape (localBank f g hs) (ports 1) (putWord g start (cs.map bitSymbol)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (caller : Tapes t 1) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (g : ℤ → Fin 5) (cs : List Bool) (hs : Fin 2 → List Bool) (start : ℕ)
    (hsrc : SharedBank.payload caller focus=sources cs g hs)
    (hv0 : Counter.value (hs 0)=start) (hv1 : Counter.value (hs 1)=cs.length) :
    HoareTime (program focus hf)
      (fun v => v=CleanSubbank.bank (s := 9) caller)
      (fun v => v=CleanSubbank.bank (s := 9) (result caller focus g cs start))
      (ActiveRepairRankFieldsField.cost start cs.length hs) := by
  have h := ActiveRepairDestinationPatchOverwrite.runs (fun _ => blank) g 0 0 cs hs start hv0 hv1
  simp only [zero_add] at h
  have hh := hoare_extend_eq h (SharedBank.empty 4 1)
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus g cs start) _ _ _ hsrc.symm ?_
    (local_clean _ _ _) (local_clean _ _ _) ?_ hh
  · rw [local_output]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem runs_linear (caller : Tapes t 1) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (g : ℤ → Fin 5) (cs : List Bool) (hs : Fin 2 → List Bool) (start : ℕ)
    (hsrc : SharedBank.payload caller focus=sources cs g hs)
    (hv0 : Counter.value (hs 0)=start) (hv1 : Counter.value (hs 1)=cs.length)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program focus hf)
      (fun v => v=CleanSubbank.bank (s := 9) caller)
      (fun v => v=CleanSubbank.bank (s := 9) (result caller focus g cs start))
      (200*(start+cs.length+1)) :=
  (runs caller focus hf g cs hs start hsrc hv0 hv1).consequence
    (fun _ h => h) (fun _ h => h) (ActiveRepairRankFieldsField.cost_linear start cs.length hs hv0 hv1 hc)

end
end IntegerMultBounds.Machine.ActiveRepairDestinationPatchPlaced
