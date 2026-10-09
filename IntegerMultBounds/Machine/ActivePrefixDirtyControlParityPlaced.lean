import IntegerMultBounds.Machine.CountedPackedParityValue
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Actual dirty compact-control parity extraction on arbitrary caller tapes.
The physical clock stream is retained, all metadata is generated and erased,
and every head is restored. Five ports are U/clock/output/b/count. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlParityPlaced
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}

def word (xs : List Bool) : ℤ → Fin (a+4) := putWord (fun _ => blank) 0 (xs.map bitSymbol)
def ports : Fin 5 → Fin 19 := Fin.castAdd 14
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective _ _
def input (U X : List Bool) (hs : Fin 2 → List Bool) :=
  CountedPackedParityRun.input (Gather.bank (word (a := a) U) (word X) (fun _ => blank) 0 0 0) hs
def sources (U X : List Bool) (hs : Fin 2 → List Bool) := SharedBank.payload (input (a := a) U X hs) ports
def result (caller : Tapes t a) (focus : Fin 5 → Fin t) (b : ℕ) (U X : List Bool) :=
  setTape caller (focus 2) (word (CountedPackedParityRun.parities b U X.length)) 0

def program (focus : Fin 5 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (CountedPackedParityRun.program a) (CleanSubbank.placement ports focus hf)

theorem clean (U X : List Bool) (hs : Fin 2 → List Bool) :
    SharedBank.strip (input (a := a) U X hs) ports=SharedBank.empty 19 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [ports,Fin.exists_fin_succ]
  all_goals rfl

theorem output_eq (U X : List Bool) (hs : Fin 2 → List Bool) (b : ℕ) :
    CountedPackedParityRun.input (Gather.bank (word (a := a) U) (word X)
      (word (CountedPackedParityRun.parities b U X.length)) 0 0 0) hs=
      result (input U X hs) ports b U X := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (caller : Tapes t a) (focus : Fin 5 → Fin t) (hf : Function.Injective focus)
    (b : ℕ) (hb : 1≤b) (U X : List Bool) (hs : Fin 2 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources U X hs)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedParityHeaders.originalValues b X.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hU : U.length=X.length*b) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 19) caller)
      (fun v => v=CleanSubbank.bank (s := 19) (result caller focus b U X))
      (330*((X.length+1)*(b+2))) := by
  have h := CountedPackedParityRun.runs (a := a) b hb U X (fun _ => blank) (fun _ => blank) 0 0 0 hs hv hc hU rfl rfl
  rw [show putWord (fun _ => blank) 0 (U.map bitSymbol)=word (a := a) U from rfl,
    show putWord (fun _ => blank) 0 (X.map bitSymbol)=word (a := a) X from rfl] at h
  rw [show putWord (fun _ => blank) 0 ((CountedPackedParityRun.parities b U X.length).map bitSymbol)=
    word (a := a) (CountedPackedParityRun.parities b U X.length) from rfl,output_eq] at h
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus b U X)
    _ _ _ hsrc.symm ?_ (clean U X hs) ?_ ?_ h
  · simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]
    exact clean U X hs
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlParityPlaced
