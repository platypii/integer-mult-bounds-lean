import IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationBudget

/-! Concrete compact conjugations on arbitrary seventeen-port caller banks.
All sixteen supplied original/prepared descriptors survive; only the full
array changes and every native private tape returns blank. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationPlaced
noncomputable section
open ActivePrefixDirtyControlConjugationData
open ActivePrefixDirtyControlConjugationSwap (count bank)
open CompactGadgetReservationShape (Shape)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

def ports (i : Fin 17) : Fin count := ⟨i.val,by have := i.isLt; unfold count; omega⟩
theorem ports_injective : Function.Injective ports := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin count => k.val) h)
def result {m : ℕ} (caller : Tapes t prime) (focus : Fin 17 → Fin t) (x : Fin m → Bool) :=
  setTape caller (focus 16) (ActiveTargetRotation.word x) 0

def tPureProgram (focus : Fin 17 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed ActivePrefixDirtyControlConjugationRun.tPureProgram (CleanSubbank.placement ports focus hf)
def tNegativeProgram (focus : Fin 17 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed ActivePrefixDirtyControlConjugationRun.tNegativeProgram (CleanSubbank.placement ports focus hf)
def uPureProgram (focus : Fin 17 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed ActivePrefixDirtyControlConjugationRun.uPureProgram (CleanSubbank.placement ports focus hf)
def uNegativeProgram (focus : Fin 17 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed ActivePrefixDirtyControlConjugationRun.uNegativeProgram (CleanSubbank.placement ports focus hf)

theorem bank_raw (v : Tapes 17 prime) : bank v=SharedBankStageInput.raw v count := by
  change (CleanSubbank.bank (s := swapCount) v).append (SharedBank.empty 65 prime)=_
  rw [SharedBankRawCompose.bank_eq_raw,SharedBankFamily.raw_append v (by omega)]
  rfl

theorem native_payload (v : Tapes 17 prime) : SharedBank.payload (bank v) ports=v := by
  rw [bank_raw]
  exact SharedBankRawCompose.payload_raw v ports (fun _ => rfl)
theorem native_clean (v : Tapes 17 prime) : SharedBank.strip (bank v) ports=SharedBank.empty count prime := by
  rw [bank_raw]
  exact SharedBankRawCompose.strip_raw v ports (fun _ => rfl)

theorem native_output {m n : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 6 → List Bool)
    (rs bs : List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    bank (base gs bw hs rs bs y)=setTape (bank (base gs bw hs rs bs x)) (ports 16) (ActiveTargetRotation.word y) 0 := by
  change ((base gs bw hs rs bs y).append (SharedBank.empty swapCount prime)).append
    (SharedBank.empty 65 prime)=setTape
    (((base gs bw hs rs bs x).append (SharedBank.empty swapCount prime)).append (SharedBank.empty 65 prime))
    (Fin.castAdd 65 (Fin.castAdd swapCount (16 : Fin 17))) _ 0
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,base_set]

theorem realizes {c budget m n : ℕ} (M : Program count c prime)
    (caller : Tapes t prime) (focus : Fin 17 → Fin t) (hf : Function.Injective focus)
    (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (x : Fin m → Bool) (y : Fin n → Bool) (hsrc : SharedBank.payload caller focus=base gs bw hs rs bs x)
    (h : HoareTime M (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs y)) budget) :
    HoareTime (Placement.placed M (CleanSubbank.placement ports focus hf))
      (fun v => v=CleanSubbank.bank (s := count) caller)
      (fun v => v=CleanSubbank.bank (s := count) (result caller focus y)) budget := by
  refine CleanSubbank.realizes M ports focus ports_injective hf caller (result caller focus y)
    _ _ _ ?_ ?_ (native_clean _) (native_clean _) ?_ h
  · exact (native_payload (base gs bw hs rs bs x)).trans hsrc.symm
  · refine (native_payload (base gs bw hs rs bs y)).trans ?_
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,base_set]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem tPure_runs (caller : Tapes t prime) (focus : Fin 17 → Fin t)
    (hf : Function.Injective focus) (s : Shape) (n rows b : ℕ)
    (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (gv : ∀ i, Counter.value (gs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s n rows i)
    (gc : ∀ i, GrowingCounterData.Canonical (gs i))
    (gb : Counter.value bw=b) (cb : GrowingCounterData.Canonical bw) (hbp : 0<b)
    (hrows : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) (hp : 0<s.payload) (hw : n*b≤s.H)
    (l : LoadShape) (B : ℕ) (hB : 0<B) (habs : l.W+l.n*l.q+l.q+l.b+1≤2^(l.n*l.b)*B)
    (hvol : rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .pure) l rows B)
    (hv : ∀ i, Counter.value (hs i)=ActivePrefixDirtyControlData.values l i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cs : GrowingCounterData.Canonical bs) (x : FullArray s rows)
    (hsrc : SharedBank.payload caller focus=base gs bw hs rs bs x) :
    HoareTime (tPureProgram focus hf) (fun v => v=CleanSubbank.bank (s := count) caller)
      (fun v => v=CleanSubbank.bank (s := count) (result caller focus
        (ActivePrefixDirtyControlConjugationRun.result .tPure s l rows (n*b) B hw hvol x)))
      (ActivePrefixDirtyControlConjugationRun.cost .tPure s rows (n*b)) :=
  realizes _ caller focus hf gs bw hs rs bs x _ hsrc
    (ActivePrefixDirtyControlConjugationRun.tPure_runs s n rows b gs bw hs rs bs gv gc gb cb hbp
      hrows hK hd hg hp hw l B hB habs hvol hv hc hr cr hb cs x)

theorem tNegative_runs (caller : Tapes t prime) (focus : Fin 17 → Fin t)
    (hf : Function.Injective focus) (s : Shape) (n rows b : ℕ)
    (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (gv : ∀ i, Counter.value (gs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s n rows i)
    (gc : ∀ i, GrowingCounterData.Canonical (gs i))
    (gb : Counter.value bw=b) (cb : GrowingCounterData.Canonical bw) (hbp : 0<b)
    (hrows : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) (hp : 0<s.payload) (hw : n*b≤s.H)
    (l : LoadShape) (B : ℕ) (hB : 0<B) (habs : l.W+l.n*l.q+l.q+l.b+1≤2^(l.n*l.b)*B)
    (hvol : rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .pure) l rows B)
    (hv : ∀ i, Counter.value (hs i)=ActivePrefixDirtyControlData.values l i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cs : GrowingCounterData.Canonical bs) (x : FullArray s rows)
    (hsrc : SharedBank.payload caller focus=base gs bw hs rs bs x) :
    HoareTime (tNegativeProgram focus hf) (fun v => v=CleanSubbank.bank (s := count) caller)
      (fun v => v=CleanSubbank.bank (s := count) (result caller focus
        (ActivePrefixDirtyControlConjugationRun.result .tNegative s l rows (n*b) B hw hvol x)))
      (ActivePrefixDirtyControlConjugationRun.cost .tNegative s rows (n*b)) :=
  realizes _ caller focus hf gs bw hs rs bs x _ hsrc
    (ActivePrefixDirtyControlConjugationRun.tNegative_runs s n rows b gs bw hs rs bs gv gc gb cb hbp
      hrows hK hd hg hp hw l B hB habs hvol hv hc hr cr hb cs x)

theorem uPure_runs (caller : Tapes t prime) (focus : Fin 17 → Fin t)
    (hf : Function.Injective focus) (s : Shape) (n rows b : ℕ)
    (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (gv : ∀ i, Counter.value (gs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s n rows i)
    (gc : ∀ i, GrowingCounterData.Canonical (gs i))
    (gb : Counter.value bw=b) (cb : GrowingCounterData.Canonical bw) (hbp : 0<b)
    (hrows : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) (hp : 0<s.payload) (hw : n*b≤s.H)
    (l : LoadShape) (B : ℕ) (hB : 0<B) (habs : l.W+l.n*l.q+l.q+l.b+1≤2^(l.n*l.b)*B)
    (hvol : rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .pure) l rows B)
    (hv : ∀ i, Counter.value (hs i)=ActivePrefixDirtyControlData.values l i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cs : GrowingCounterData.Canonical bs) (x : FullArray s rows)
    (hsrc : SharedBank.payload caller focus=base gs bw hs rs bs x) :
    HoareTime (uPureProgram focus hf) (fun v => v=CleanSubbank.bank (s := count) caller)
      (fun v => v=CleanSubbank.bank (s := count) (result caller focus
        (ActivePrefixDirtyControlConjugationRun.result .uPure s l rows (n*b) B hw hvol x)))
      (ActivePrefixDirtyControlConjugationRun.cost .uPure s rows (n*b)) :=
  realizes _ caller focus hf gs bw hs rs bs x _ hsrc
    (ActivePrefixDirtyControlConjugationRun.uPure_runs s n rows b gs bw hs rs bs gv gc gb cb hbp
      hrows hK hd hg hp hw l B hB habs hvol hv hc hr cr hb cs x)

theorem uNegative_runs (caller : Tapes t prime) (focus : Fin 17 → Fin t)
    (hf : Function.Injective focus) (s : Shape) (n rows b : ℕ)
    (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 6 → List Bool) (rs bs : List Bool)
    (gv : ∀ i, Counter.value (gs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s n rows i)
    (gc : ∀ i, GrowingCounterData.Canonical (gs i))
    (gb : Counter.value bw=b) (cb : GrowingCounterData.Canonical bw) (hbp : 0<b)
    (hrows : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) (hp : 0<s.payload) (hw : n*b≤s.H)
    (l : LoadShape) (B : ℕ) (hB : 0<B) (habs : l.W+l.n*l.q+l.q+l.b+1≤2^(l.n*l.b)*B)
    (hvol : rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .pure) l rows B)
    (hv : ∀ i, Counter.value (hs i)=ActivePrefixDirtyControlData.values l i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cs : GrowingCounterData.Canonical bs) (x : FullArray s rows)
    (hsrc : SharedBank.payload caller focus=base gs bw hs rs bs x) :
    HoareTime (uNegativeProgram focus hf) (fun v => v=CleanSubbank.bank (s := count) caller)
      (fun v => v=CleanSubbank.bank (s := count) (result caller focus
        (ActivePrefixDirtyControlConjugationRun.result .uNegative s l rows (n*b) B hw hvol x)))
      (ActivePrefixDirtyControlConjugationRun.cost .uNegative s rows (n*b)) :=
  realizes _ caller focus hf gs bw hs rs bs x _ hsrc
    (ActivePrefixDirtyControlConjugationRun.uNegative_runs s n rows b gs bw hs rs bs gv gc gb cb hbp
      hrows hK hd hg hp hw l B hB habs hvol hv hc hr cr hb cs x)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationPlaced
