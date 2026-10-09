import IntegerMultBounds.Machine.ActivePrefixDirtyControlLoad

/-! The complete original-input dirty-U load actions on arbitrary caller
tapes. Eight original headers and the array are permanent; all private storage
starts and returns blank, with arbitrary caller spectators unchanged. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadPlaced
noncomputable section
open ActivePrefixDirtyControlLoadData
open ActivePrefixDirtyControlLoadProducer (Mode Shape values width)
open ActivePrefixDirtyControlLoadHeaders (bank)
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ} {m : Mode}

def ports : Fin 9 → Fin 65 := Fin.castAdd 56
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective _ _

def sources (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) := SharedBank.payload (bank (base (a := a) s rows B hs rs bs x)) ports

def result (caller : Tapes t a) (focus : Fin 9 → Fin t) (s : Shape m) (rows B : ℕ) (x : Array s rows B) :=
  setTape caller (focus 8) (ActiveTargetRotation.word (ActivePrefixDirtyControlLoad.result s rows B x)) 0

def program (m : Mode) (focus : Fin 9 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixDirtyControlLoad.program (a := a) m) (CleanSubbank.placement ports focus hf)

theorem native_clean (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) :
    SharedBank.strip (bank (base (a := a) s rows B hs rs bs x)) ports=SharedBank.empty 65 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [bank,CleanSubbank.bank,Tapes.append,SharedBank.empty,base,ports,Fin.exists_fin_succ]
  all_goals rfl

theorem native_output (s : Shape m) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) :
    bank (base (a := a) s rows B hs rs bs (ActivePrefixDirtyControlLoad.result s rows B x))=
      setTape (bank (base s rows B hs rs bs x)) (ports 8)
        (ActiveTargetRotation.word (ActivePrefixDirtyControlLoad.result s rows B x)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (caller : Tapes t a) (focus : Fin 9 → Fin t) (hf : Function.Injective focus)
    (s : Shape m) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B) (habs : s.W+s.n*s.q+s.q+s.b+1≤2^width s*B)
    (hs : Fin 6 → List Bool) (rs bs : List Bool) (x : Array s rows B)
    (hsrc : SharedBank.payload caller focus=sources s rows B hs rs bs x)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program m focus hf) (fun v => v=CleanSubbank.bank (s := 65) caller)
      (fun v => v=CleanSubbank.bank (s := 65) (result caller focus s rows B x))
      (ActivePrefixDirtyControlLoad.constant*volume s rows B) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus s rows B x)
    _ _ _ hsrc.symm ?_ (native_clean s rows B hs rs bs x)
    (native_clean s rows B hs rs bs _) ?_
    (ActivePrefixDirtyControlLoad.runs_linear s rows B hrows hB habs hs rs bs x hv hc hr cr hb cb)
  · rw [native_output]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem frame (caller : Tapes t a) (focus : Fin 9 → Fin t) (s : Shape m) (rows B : ℕ)
    (x : Array s rows B) (i : Fin t) (hi : i≠focus 8) :
    (result caller focus s rows B x).head i=caller.head i ∧
    (result caller focus s rows B x).tape i=caller.tape i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadPlaced
