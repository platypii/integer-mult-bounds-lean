import IntegerMultBounds.Machine.ActivePrefixCompactConjugationMiddle

/-! Paid physical swap/load/swap with literal serialized-array transport.
The supplied load shape describes the actual prefix and source coordinates;
stage-control preparation of its eight numeric words remains separate. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactConjugationRun
noncomputable section
open ActivePrefixCompactConjugationData
open ActivePrefixCompactConjugationMiddle (bank)
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)

def swap (kind : Kind) := extend (ActivePrefixCompactSwapPlaced.program swapFocus swap_injective) (privateCount kind)
def program (kind : Kind) := seq (seq (swap kind) (ActivePrefixCompactConjugationMiddle.program kind)) (swap kind)

def middle (kind : Kind) (s : Shape) (l : ActivePrefixParityOnlyBank.Shape) (rows w B : ℕ)
    (hvol : ActivePrefixCompactSwapData.volume s rows w=ActivePrefixCompactParityLoadData.volume l rows B)
    (x : ActivePrefixCompactSwapData.Array s rows w) : ActivePrefixCompactSwapData.Array s rows w :=
  view hvol.symm (loadResult kind l rows B (view hvol (RadixRangePadding.transpose x)))
def result (kind : Kind) (s : Shape) (l : ActivePrefixParityOnlyBank.Shape) (rows w B : ℕ)
    (hvol : ActivePrefixCompactSwapData.volume s rows w=ActivePrefixCompactParityLoadData.volume l rows B)
    (x : ActivePrefixCompactSwapData.Array s rows w) :=
  RadixRangePadding.transpose (middle kind s l rows w B hvol x)
def cost (kind : Kind) (s : Shape) (rows w : ℕ) :=
  2*ActivePrefixCompactSwapRun.cost s rows w+constant kind*ActivePrefixCompactSwapData.volume s rows w+2

variable (kind : Kind) (s : Shape) (n rows b : ℕ)
variable (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 8 → List Bool) (rs bs : List Bool)
variable (gv : ∀ i, Counter.value (gs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s n rows i)
variable (gc : ∀ i, GrowingCounterData.Canonical (gs i))
variable (gb : Counter.value bw=b) (cb : GrowingCounterData.Canonical bw) (hbp : 0<b)
variable (hrows : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard) (hp : 0<s.payload) (hw : n*b≤s.H)

include gv gc gb cb hbp hrows hK hd hg hp hw in
theorem swap_runs (x : ActivePrefixCompactSwapData.Array s rows (n*b)) :
    HoareTime (swap kind) (fun v => v=bank kind (base gs bw hs rs bs x))
      (fun v => v=bank kind (base gs bw hs rs bs (RadixRangePadding.transpose x)))
      (ActivePrefixCompactSwapRun.cost s rows (n*b)) := by
  have h := ActivePrefixCompactSwapPlaced.runs (base gs bw hs rs bs x) swapFocus swap_injective s n rows b gs bw x
    (swap_sources s rows (n*b) gs bw hs rs bs x) gv gc gb cb hbp hrows hK hd hg hp hw
  have hout : ActivePrefixCompactSwapPlaced.result (base gs bw hs rs bs x) swapFocus x=
      base gs bw hs rs bs (RadixRangePadding.transpose x) := by
    exact base_set gs bw hs rs bs x (RadixRangePadding.transpose x)
  rw [hout] at h
  exact hoare_extend_eq h (SharedBank.empty (privateCount kind) prime)

include gv gc gb cb hbp hrows hK hd hg hp hw in
theorem runs (l : ActivePrefixParityOnlyBank.Shape) (B : ℕ) (hB : 0<B)
    (habs : l.W+1≤2^(l.n*l.b)*B)
    (hvol : ActivePrefixCompactSwapData.volume s rows (n*b)=ActivePrefixCompactParityLoadData.volume l rows B)
    (hv : ∀ i, Counter.value (hs i)=ActivePrefixParityOnlyBank.values l i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
    (hb : Counter.value bs=B) (cs : GrowingCounterData.Canonical bs)
    (x : ActivePrefixCompactSwapData.Array s rows (n*b)) :
    HoareTime (program kind) (fun v => v=bank kind (base gs bw hs rs bs x))
      (fun v => v=bank kind (base gs bw hs rs bs (result kind s l rows (n*b) B hvol x)))
      (cost kind s rows (n*b)) := by
  have h₀ := swap_runs kind s n rows b gs bw hs rs bs gv gc gb cb hbp hrows hK hd hg hp hw x
  have hm := ActivePrefixCompactConjugationMiddle.runs kind l rows B hrows hB habs gs bw hs rs bs
    (view hvol (RadixRangePadding.transpose x)) hv hc hr cr hb cs
  have he : base gs bw hs rs bs (loadResult kind l rows B (view hvol (RadixRangePadding.transpose x)))=
      base gs bw hs rs bs (middle kind s l rows (n*b) B hvol x) := (base_view hvol.symm gs bw hs rs bs _).symm
  rw [base_view,he] at hm
  have h₁ := swap_runs kind s n rows b gs bw hs rs bs gv gc gb cb hbp hrows hK hd hg hp hw
    (middle kind s l rows (n*b) B hvol x)
  exact ((h₀.seq hm).seq h₁).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost; rw [hvol]; omega)

end
end IntegerMultBounds.Machine.ActivePrefixCompactConjugationRun
