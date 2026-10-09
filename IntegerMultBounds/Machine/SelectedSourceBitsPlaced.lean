import IntegerMultBounds.Machine.SelectedSourceBitsRun
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Selected bits are extracted from the actual complete caller source tape.
Six caller ports are source/output/q/n/rho/f; the output starts blank. Source,
original headers and arbitrary spectators are retained with their heads. -/
namespace IntegerMultBounds.Machine.SelectedSourceBitsPlaced
noncomputable section
open SelectedSourceBitsData
open SelectedSourceBitsScan (word)
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

def ports : Fin 6 → Fin 9 := ![0,1,3,5,7,8]
theorem ports_injective : Function.Injective ports := by decide

def sources (xs : List Bool) (hs : Fin 4 → List Bool) : Tapes 6 a :=
  SharedBank.payload (SelectedSourceBitsRun.input xs hs) ports

def result (caller : Tapes t a) (focus : Fin 6 → Fin t) (xs : List Bool) (q rho n : ℕ) :=
  setTape caller (focus 1) (word (selected xs q rho n)) 0

def program (focus : Fin 6 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (SelectedSourceBitsRun.program (a := a)) (CleanSubbank.placement ports focus hf)

theorem clean (xs : List Bool) (hs : Fin 4 → List Bool) :
    SharedBank.strip (SelectedSourceBitsRun.input (a := a) xs hs) ports = SharedBank.empty 9 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [SelectedSourceBitsRun.input,SelectedSourceBitsBank.raw,
    CountedBankResetHeader.rawBank,SelectedSourceBitsCore.payload,SelectedSourceBitsScan.word,
    Tapes.append,Fin.addCases,ports,Fin.exists_fin_succ]
  all_goals rfl

theorem output_eq (xs : List Bool) (hs : Fin 4 → List Bool) (q rho n : ℕ) :
    SelectedSourceBitsRun.output (a := a) xs hs q rho n =
      setTape (SelectedSourceBitsRun.input xs hs) (ports 1) (word (selected xs q rho n)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (caller : Tapes t a) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (xs : List Bool) (hs : Fin 4 → List Bool) (q rho n f : ℕ)
    (hsrc : SharedBank.payload caller focus=sources xs hs)
    (hxs : xs.length=f*q) (hnf : n+1=f) (hr : rho<q)
    (hv : ∀ i, Counter.value (hs i)=SelectedSourceBitsRun.values q n rho f i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a) focus hf)
      (fun v => v=CleanSubbank.bank (s := 9) caller)
      (fun v => v=CleanSubbank.bank (s := 9) (result caller focus xs q rho n))
      (400*xs.length) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus xs q rho n) _ _ _ hsrc.symm ?_ (clean xs hs) ?_ ?_
    (SelectedSourceBitsRun.runs_linear xs hs q rho n f hxs hnf hr hv hc)
  · rw [output_eq]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · rw [output_eq,CompactGadgetReservationPlacement.strip_set]
    exact clean xs hs
  · simp only [result,CompactGadgetReservationPlacement.strip_set]


theorem result_word (caller : Tapes t a) (focus : Fin 6 → Fin t) (xs : List Bool) (q rho n : ℕ) :
    (result caller focus xs q rho n).tape (focus 1) =
      putWord (fun _ => blank) 0
        (((List.range n).map (fun i => Nat.testBit (Counter.value xs) (rho+i*q))).map bitSymbol) ∧
    (result caller focus xs q rho n).head (focus 1) = 0 := by
  simp [result,setTape,word,selected_testBit]

theorem frame (caller : Tapes t a) (focus : Fin 6 → Fin t) (xs : List Bool) (q rho n : ℕ)
    (i : Fin t) (hi : i ≠ focus 1) :
    (result caller focus xs q rho n).tape i = caller.tape i ∧
      (result caller focus xs q rho n).head i = caller.head i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.SelectedSourceBitsPlaced
