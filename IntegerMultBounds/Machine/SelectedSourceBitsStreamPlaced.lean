import IntegerMultBounds.Machine.SelectedSourceBitsStreamRun
import IntegerMultBounds.Machine.CompactGadgetReservationPlacement

/-! Selected bits are extracted from every complete row of the caller source stream.
Seven caller ports are source/output/q/n/rho/f/P; the output starts blank. Source,
original headers and arbitrary spectators are retained with their heads. -/
namespace IntegerMultBounds.Machine.SelectedSourceBitsStreamPlaced
noncomputable section
open SelectedSourceBitsStreamData
open SelectedSourceBitsScan (word)
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

def ports : Fin 7 → Fin 11 := ![0,1,3,5,7,10,9]
theorem ports_injective : Function.Injective ports := by decide

def sources (xs : List Bool) (hs : Fin 5 → List Bool) : Tapes 7 a :=
  SharedBank.payload (SelectedSourceBitsStreamRun.input xs hs) ports

def result (caller : Tapes t a) (focus : Fin 7 → Fin t) (xs : List Bool) (q rho n f P : ℕ) :=
  setTape caller (focus 1) (word (selected xs q rho n f P)) 0

def program (focus : Fin 7 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (SelectedSourceBitsStreamRun.program (a := a)) (CleanSubbank.placement ports focus hf)

theorem clean (xs : List Bool) (hs : Fin 5 → List Bool) :
    SharedBank.strip (SelectedSourceBitsStreamRun.input (a := a) xs hs) ports = SharedBank.empty 11 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [SelectedSourceBitsStreamRun.input,SelectedSourceBitsStreamBank.raw,
    SelectedSourceBitsCore.payload,SelectedSourceBitsScan.word,
    Tapes.append,Fin.addCases,ports,Fin.exists_fin_succ]
  all_goals rfl

theorem output_eq (xs : List Bool) (hs : Fin 5 → List Bool) (q rho n f P : ℕ) :
    SelectedSourceBitsStreamRun.output (a := a) xs hs q rho n f P =
      setTape (SelectedSourceBitsStreamRun.input xs hs) (ports 1) (word (selected xs q rho n f P)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (caller : Tapes t a) (focus : Fin 7 → Fin t) (hf : Function.Injective focus)
    (xs : List Bool) (hs : Fin 5 → List Bool) (q rho n f P : ℕ)
    (hsrc : SharedBank.payload caller focus=sources xs hs)
    (hxs : xs.length=P*(f*q)) (hnf : n+1=f) (hr : rho<q)
    (hv : ∀ i, Counter.value (hs i)=SelectedSourceBitsStreamRun.values q n rho f P i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a) focus hf)
      (fun v => v=CleanSubbank.bank (s := 11) caller)
      (fun v => v=CleanSubbank.bank (s := 11) (result caller focus xs q rho n f P))
      (400*(xs.length+1)) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller
    (result caller focus xs q rho n f P) _ _ _ hsrc.symm ?_ (clean xs hs) ?_ ?_
    (SelectedSourceBitsStreamRun.runs_linear xs hs q rho n f P hxs hnf hr hv hc)
  · rw [output_eq]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · rw [output_eq,CompactGadgetReservationPlacement.strip_set]
    exact clean xs hs
  · simp only [result,CompactGadgetReservationPlacement.strip_set]


theorem result_word (caller : Tapes t a) (focus : Fin 7 → Fin t) (xs : List Bool) (q rho n f P : ℕ) :
    (result caller focus xs q rho n f P).tape (focus 1) =
      putWord (fun _ => blank) 0
        (((List.range P).flatMap (fun r => (List.range n).map
          (fun i => Nat.testBit (Counter.value xs) (r*(f*q)+rho+i*q)))).map bitSymbol) ∧
    (result caller focus xs q rho n f P).head (focus 1) = 0 := by
  simp [result,setTape,word,selected_testBit]

theorem frame (caller : Tapes t a) (focus : Fin 7 → Fin t) (xs : List Bool) (q rho n f P : ℕ)
    (i : Fin t) (hi : i ≠ focus 1) :
    (result caller focus xs q rho n f P).tape i = caller.tape i ∧
      (result caller focus xs q rho n f P).head i = caller.head i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.SelectedSourceBitsStreamPlaced
