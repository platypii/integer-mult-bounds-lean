import IntegerMultBounds.Machine.ActivePrefixSelectedLoad

/-! The complete original-input selected load on arbitrary caller
tapes. Ten original headers and the array are permanent; all private storage
starts and returns blank, with arbitrary caller spectators unchanged. -/
namespace IntegerMultBounds.Machine.ActivePrefixSelectedLoadPlaced
noncomputable section
open ActivePrefixSelectedLoadData
open ActivePrefixSelectedOffsetBank (Shape values)
open ActivePrefixSelectedLoadHeaders (bank)
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}

def ports : Fin 11 → Fin 60 := Fin.castAdd 49
theorem ports_injective : Function.Injective ports := Fin.castAdd_injective _ _

def sources (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) := SharedBank.payload (bank (base (a := a) s rows B hs rs bs x)) ports

/-- Literal eleven permanent ports: original eight, rows, B, full array. -/
theorem sources_eq (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) : sources (a := a) s rows B hs rs bs x=
      (⟨fun i => if i.val<10 then 1 else 0,
        fun i => if h : i.val<8 then RadixZeroFill.encodedBinary (hs ⟨i.val,h⟩)
          else if i.val=8 then RadixZeroFill.encodedBinary rs
          else if i.val=9 then RadixZeroFill.encodedBinary bs
          else ActiveTargetRotation.word x⟩ : Tapes 11 a) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def result (caller : Tapes t a) (focus : Fin 11 → Fin t) (s : Shape) (rows B : ℕ) (x : Array s rows B) :=
  setTape caller (focus 10) (ActiveTargetRotation.word (ActivePrefixSelectedLoad.result s rows B x)) 0

def program (focus : Fin 11 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixSelectedLoad.program (a := a)) (CleanSubbank.placement ports focus hf)

theorem native_clean (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) :
    SharedBank.strip (bank (base (a := a) s rows B hs rs bs x)) ports=SharedBank.empty 60 a := by
  have hex (i : Fin 60) : (∃ j, ports j=i) ↔ i.val<11 := by
    constructor
    · rintro ⟨j,rfl⟩; exact j.isLt
    · intro h
      exact ⟨⟨i.val,h⟩,Fin.ext rfl⟩
  have he (i : Fin 60) :
      (SharedBank.strip (bank (base (a := a) s rows B hs rs bs x)) ports).head i=0 ∧
      (SharedBank.strip (bank (base (a := a) s rows B hs rs bs x)) ports).tape i=(fun _ => blank) := by
    by_cases hi : i.val<11
    · simp [SharedBank.strip,hex,hi]
    · have hblank := ActivePrefixSelectedLoad.result_blank (a := a) s rows B hs rs bs x i (by omega)
      have hframe := ActivePrefixSelectedLoad.result_frame (a := a) s rows B hs rs bs x i (by omega)
      simpa only [SharedBank.strip,hex,hi,↓reduceIte,hframe.1,hframe.2] using hblank
  apply congrArg₂ Tapes.mk
  · funext i; exact (he i).1
  · funext i; exact (he i).2

theorem native_output (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) :
    bank (base (a := a) s rows B hs rs bs (ActivePrefixSelectedLoad.result s rows B x))=
      setTape (bank (base s rows B hs rs bs x)) (ports 10)
        (ActiveTargetRotation.word (ActivePrefixSelectedLoad.result s rows B x)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs_exact (caller : Tapes t a) (focus : Fin 11 → Fin t) (hf : Function.Injective focus)
    (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : Array s rows B)
    (hsrc : SharedBank.payload caller focus=sources s rows B hs rs bs x)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 60) caller)
      (fun v => v=CleanSubbank.bank (s := 60) (result caller focus s rows B x))
      (ActivePrefixSelectedLoad.cost s rows B) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus s rows B x)
    _ _ _ hsrc.symm ?_ (native_clean s rows B hs rs bs x)
    (native_clean s rows B hs rs bs _) ?_
    (ActivePrefixSelectedLoad.runs s rows B hrows hB hs rs bs x hv hc hr cr hb cb)
  · rw [native_output]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem runs (caller : Tapes t a) (focus : Fin 11 → Fin t) (hf : Function.Injective focus)
    (s : Shape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B) (habs : s.W+1≤2^width s*B)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : Array s rows B)
    (hsrc : SharedBank.payload caller focus=sources s rows B hs rs bs x)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := 60) caller)
      (fun v => v=CleanSubbank.bank (s := 60) (result caller focus s rows B x))
      (ActivePrefixSelectedLoad.constant*volume s rows B) :=
  (runs_exact caller focus hf s rows B hrows hB hs rs bs x hsrc hv hc hr cr hb cb).consequence
    (fun _ h => h) (fun _ h => h) (ActivePrefixSelectedLoad.cost_bound s rows B hrows hB habs)

theorem frame (caller : Tapes t a) (focus : Fin 11 → Fin t) (s : Shape) (rows B : ℕ)
    (x : Array s rows B) (i : Fin t) (hi : i≠focus 10) :
    (result caller focus s rows B x).head i=caller.head i ∧
    (result caller focus s rows B x).tape i=caller.tape i := by
  simp [result,setTape,hi]
theorem result_payload (caller : Tapes t a) (focus : Fin 11 → Fin t) (s : Shape) (rows B : ℕ)
    (x : Array s rows B) :
    (result caller focus s rows B x).head (focus 10)=0 ∧
    (result caller focus s rows B x).tape (focus 10)=
      ActiveTargetRotation.word (ActivePrefixSelectedLoad.result s rows B x) := by
  simp [result,setTape]

end
end IntegerMultBounds.Machine.ActivePrefixSelectedLoadPlaced
