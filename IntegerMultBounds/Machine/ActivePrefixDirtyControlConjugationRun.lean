import IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationMiddle

/-! Physical T/back or U/back swap, actual compact load, and physical swap
back. Original caller words survive and every private tape is restored blank. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationRun
noncomputable section
open ActivePrefixDirtyControlConjugationData
open ActivePrefixDirtyControlConjugationSwap (bank count)
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)

def tProgram (kind : Kind) := seq (seq ActivePrefixDirtyControlConjugationSwap.tProgram
  (ActivePrefixDirtyControlConjugationMiddle.program kind)) ActivePrefixDirtyControlConjugationSwap.tProgram
def uProgram (kind : Kind) := seq (seq ActivePrefixDirtyControlConjugationSwap.uProgram
  (ActivePrefixDirtyControlConjugationMiddle.program kind)) ActivePrefixDirtyControlConjugationSwap.uProgram
def tPureProgram := tProgram .tPure
def tNegativeProgram := tProgram .tNegative
def uPureProgram := uProgram .uPure
def uNegativeProgram := uProgram .uNegative

def loaded (kind : Kind) (s : Shape) (l : LoadShape) (rows B : ℕ)
    (hvol : rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .pure) l rows B)
    (x : FullArray s rows) : FullArray s rows := view hvol.symm (loadResult kind l rows B (view hvol x))
def result (kind : Kind) (s : Shape) (l : LoadShape) (rows w B : ℕ) (hw : w≤s.H)
    (hvol : rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .pure) l rows B)
    (x : FullArray s rows) :=
  swapped kind s rows w hw (loaded kind s l rows B hvol (swapped kind s rows w hw x))
def cost (kind : Kind) (s : Shape) (rows w : ℕ) := 2*swapCost kind s rows w+loadConstant kind*(rows*s.recordWidth)+2

def tResult (kind : Kind) (s : Shape) (l : LoadShape) (rows w B : ℕ) (hw : w≤s.H)
    (hvol : rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .pure) l rows B)
    (x : FullArray s rows) := tSwap s rows w hw (loaded kind s l rows B hvol (tSwap s rows w hw x))
def uResult (kind : Kind) (s : Shape) (l : LoadShape) (rows w B : ℕ) (hw : w≤s.H)
    (hvol : rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .pure) l rows B)
    (x : FullArray s rows) := uSwap s rows w hw (loaded kind s l rows B hvol (uSwap s rows w hw x))
def tCost (kind : Kind) (s : Shape) (rows w : ℕ) :=
  2*ActivePrefixCompactSwapRun.cost s rows w+loadConstant kind*(rows*s.recordWidth)+2
def uCost (kind : Kind) (s : Shape) (rows w : ℕ) :=
  2*ActivePrefixDirtyControlUSwapRun.cost s rows w+loadConstant kind*(rows*s.recordWidth)+2

theorem t_runs (kind : Kind) (s : Shape) (n rows b : ℕ)
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
    (hb : Counter.value bs=B) (cs : GrowingCounterData.Canonical bs) (x : FullArray s rows) :
    HoareTime (tProgram kind) (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs (tResult kind s l rows (n*b) B hw hvol x)))
      (tCost kind s rows (n*b)) := by
  have h₀ := ActivePrefixDirtyControlConjugationSwap.t_runs s n rows b gs bw hs rs bs gv gc gb cb hbp
    hrows hK hd hg hp hw x
  let y := tSwap s rows (n*b) hw x
  have hm := ActivePrefixDirtyControlConjugationMiddle.runs l rows B hrows hB habs gs bw hs rs bs hv hc hr cr hb cs
    kind (view hvol y)
  have he : base gs bw hs rs bs (loadResult kind l rows B (view hvol y))=
      base gs bw hs rs bs (loaded kind s l rows B hvol y) := (base_view hvol.symm _ _ _ _ _ _).symm
  rw [base_view,he] at hm
  have h₁ := ActivePrefixDirtyControlConjugationSwap.t_runs s n rows b gs bw hs rs bs gv gc gb cb hbp
    hrows hK hd hg hp hw (loaded kind s l rows B hvol y)
  exact ((h₀.seq hm).seq h₁).consequence (fun _ h => h) (fun _ h => h)
    (by unfold tCost; rw [hvol]; omega)


theorem u_runs (kind : Kind) (s : Shape) (n rows b : ℕ)
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
    (hb : Counter.value bs=B) (cs : GrowingCounterData.Canonical bs) (x : FullArray s rows) :
    HoareTime (uProgram kind) (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs (uResult kind s l rows (n*b) B hw hvol x)))
      (uCost kind s rows (n*b)) := by
  have h₀ := ActivePrefixDirtyControlConjugationSwap.u_runs s n rows b gs bw hs rs bs gv gc gb cb hbp
    hrows hK hd hg hp hw x
  let y := uSwap s rows (n*b) hw x
  have hm := ActivePrefixDirtyControlConjugationMiddle.runs l rows B hrows hB habs gs bw hs rs bs hv hc hr cr hb cs
    kind (view hvol y)
  have he : base gs bw hs rs bs (loadResult kind l rows B (view hvol y))=
      base gs bw hs rs bs (loaded kind s l rows B hvol y) := (base_view hvol.symm _ _ _ _ _ _).symm
  rw [base_view,he] at hm
  have h₁ := ActivePrefixDirtyControlConjugationSwap.u_runs s n rows b gs bw hs rs bs gv gc gb cb hbp
    hrows hK hd hg hp hw (loaded kind s l rows B hvol y)
  exact ((h₀.seq hm).seq h₁).consequence (fun _ h => h) (fun _ h => h)
    (by unfold uCost; rw [hvol]; omega)


theorem tPure_runs (s : Shape) (n rows b : ℕ)
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
    (hb : Counter.value bs=B) (cs : GrowingCounterData.Canonical bs) (x : FullArray s rows) :
    HoareTime tPureProgram (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs (result .tPure s l rows (n*b) B hw hvol x)))
      (cost .tPure s rows (n*b)) :=
  t_runs .tPure s n rows b gs bw hs rs bs gv gc gb cb hbp hrows hK hd hg hp hw
    l B hB habs hvol hv hc hr cr hb cs x


theorem tNegative_runs (s : Shape) (n rows b : ℕ)
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
    (hb : Counter.value bs=B) (cs : GrowingCounterData.Canonical bs) (x : FullArray s rows) :
    HoareTime tNegativeProgram (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs (result .tNegative s l rows (n*b) B hw hvol x)))
      (cost .tNegative s rows (n*b)) :=
  t_runs .tNegative s n rows b gs bw hs rs bs gv gc gb cb hbp hrows hK hd hg hp hw
    l B hB habs hvol hv hc hr cr hb cs x


theorem uPure_runs (s : Shape) (n rows b : ℕ)
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
    (hb : Counter.value bs=B) (cs : GrowingCounterData.Canonical bs) (x : FullArray s rows) :
    HoareTime uPureProgram (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs (result .uPure s l rows (n*b) B hw hvol x)))
      (cost .uPure s rows (n*b)) :=
  u_runs .uPure s n rows b gs bw hs rs bs gv gc gb cb hbp hrows hK hd hg hp hw
    l B hB habs hvol hv hc hr cr hb cs x


theorem uNegative_runs (s : Shape) (n rows b : ℕ)
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
    (hb : Counter.value bs=B) (cs : GrowingCounterData.Canonical bs) (x : FullArray s rows) :
    HoareTime uNegativeProgram (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs (result .uNegative s l rows (n*b) B hw hvol x)))
      (cost .uNegative s rows (n*b)) :=
  u_runs .uNegative s n rows b gs bw hs rs bs gv gc gb cb hbp hrows hK hd hg hp hw
    l B hB habs hvol hv hc hr cr hb cs x

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationRun
