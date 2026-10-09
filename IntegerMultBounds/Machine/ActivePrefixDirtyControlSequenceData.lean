import IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationPlaced

/-! The literal later-source schedule on one unchanged array. All three
six-header groups describe real producer coordinates; no offset stream or
load action is supplied by the caller. Header synthesis remains separate. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceData
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open ActivePrefixDirtyControlConjugationData (FullArray LoadShape view)
open SharedPlacementAlphabet (setTape)

structure Geometry (s : Shape) where
  n : ℕ
  b : ℕ
  rows : ℕ
  target : ActivePrefixDirtyControlData.Shape .selected
  compact : LoadShape
  source : LoadShape
  targetSuffix : ℕ
  compactSuffix : ℕ
  compactFits : n*b≤s.H
  targetVolume : rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .selected) target rows targetSuffix
  compactVolume : rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .pure) compact rows compactSuffix
  sourceVolume : rows*s.recordWidth=ActivePrefixDirtyControlLoadData.volume (m := .pure) source rows compactSuffix
  targetAbsorbed : target.W+target.n*target.q+target.q+target.b+1≤2^(target.n*target.q)*targetSuffix
  compactAbsorbed : compact.W+compact.n*compact.q+compact.q+compact.b+1≤2^(compact.n*compact.b)*compactSuffix
  sourceAbsorbed : source.W+source.n*source.q+source.q+source.b+1≤2^(source.n*source.b)*compactSuffix
  positiveRows : 0<rows
  positiveWidth : 0<b
  positiveTargetSuffix : 0<targetSuffix
  positiveCompactSuffix : 0<compactSuffix
  positiveChunk : 0<s.chunk
  positiveAxes : 0<s.axes
  positiveGuard : 0<s.guard
  positivePayload : 0<s.payload

structure Inputs (s : Shape) (g : Geometry s) where
  gs : Fin 7 → List Bool
  bw : List Bool
  ht : Fin 6 → List Bool
  hc : Fin 6 → List Bool
  hx : Fin 6 → List Bool
  rs : List Bool
  bt : List Bool
  bc : List Bool
  gv : ∀ i, Counter.value (gs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s g.n g.rows i
  gc : ∀ i, GrowingCounterData.Canonical (gs i)
  gb : Counter.value bw=g.b
  cb : GrowingCounterData.Canonical bw
  tv : ∀ i, Counter.value (ht i)=ActivePrefixDirtyControlData.values g.target i
  tc : ∀ i, GrowingCounterData.Canonical (ht i)
  cv : ∀ i, Counter.value (hc i)=ActivePrefixDirtyControlData.values g.compact i
  cc : ∀ i, GrowingCounterData.Canonical (hc i)
  xv : ∀ i, Counter.value (hx i)=ActivePrefixDirtyControlData.values g.source i
  xc : ∀ i, GrowingCounterData.Canonical (hx i)
  rv : Counter.value rs=g.rows
  rc : GrowingCounterData.Canonical rs
  btv : Counter.value bt=g.targetSuffix
  btc : GrowingCounterData.Canonical bt
  bcv : Counter.value bc=g.compactSuffix
  bcc : GrowingCounterData.Canonical bc

variable {s : Shape} {g : Geometry s}

def targetFocus : Fin 9 → Fin 30 := ![8,9,10,11,12,13,26,27,29]
def compactFocus : Fin 17 → Fin 30 := ![0,1,2,3,4,5,6,7,14,15,16,17,18,19,26,28,29]
def sourceFocus : Fin 17 → Fin 30 := ![0,1,2,3,4,5,6,7,20,21,22,23,24,25,26,28,29]
theorem target_injective : Function.Injective targetFocus := by decide
theorem compact_injective : Function.Injective compactFocus := by decide
theorem source_injective : Function.Injective sourceFocus := by decide

def caller {m : ℕ} (d : Inputs s g) (x : Fin m → Bool) : Tapes 30 prime :=
  ⟨fun i => if i.val<29 then 1 else 0,
    fun i => if h : i.val<7 then RadixZeroFill.encodedBinary (d.gs ⟨i.val,h⟩)
      else if i.val=7 then RadixZeroFill.encodedBinary d.bw
      else if h : i.val<14 then RadixZeroFill.encodedBinary (d.ht ⟨i.val-8,by omega⟩)
      else if h : i.val<20 then RadixZeroFill.encodedBinary (d.hc ⟨i.val-14,by omega⟩)
      else if h : i.val<26 then RadixZeroFill.encodedBinary (d.hx ⟨i.val-20,by omega⟩)
      else if i.val=26 then RadixZeroFill.encodedBinary d.rs
      else if i.val=27 then RadixZeroFill.encodedBinary d.bt
      else if i.val=28 then RadixZeroFill.encodedBinary d.bc
      else ActiveTargetRotation.word x⟩

theorem caller_view {m n : ℕ} (h : m=n) (d : Inputs s g) (x : Fin m → Bool) :
    caller d (view h x)=caller d x := by unfold caller; rw [ActivePrefixDirtyControlConjugationData.word_view]
theorem caller_set {m n : ℕ} (d : Inputs s g) (x : Fin m → Bool) (y : Fin n → Bool) :
    setTape (caller d x) 29 (ActiveTargetRotation.word y) 0=caller d y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def selected (g : Geometry s) (x : FullArray s g.rows) : FullArray s g.rows :=
  view g.targetVolume.symm (ActivePrefixDirtyControlLoad.result (m := .selected) g.target g.rows g.targetSuffix (view g.targetVolume x))
def correction (g : Geometry s) (x : FullArray s g.rows) : FullArray s g.rows :=
  view g.targetVolume.symm (ActivePrefixDirtyControlLoad.result (m := .correction) g.target g.rows g.targetSuffix (view g.targetVolume x))
def pure (g : Geometry s) (x : FullArray s g.rows) :=
  ActivePrefixDirtyControlConjugationRun.result .tPure s g.compact g.rows (g.n*g.b) g.compactSuffix g.compactFits g.compactVolume x
def negative (g : Geometry s) (x : FullArray s g.rows) :=
  ActivePrefixDirtyControlConjugationRun.result .tNegative s g.compact g.rows (g.n*g.b) g.compactSuffix g.compactFits g.compactVolume x
def load (g : Geometry s) (x : FullArray s g.rows) :=
  ActivePrefixDirtyControlConjugationRun.result .uPure s g.source g.rows (g.n*g.b) g.compactSuffix g.compactFits g.sourceVolume x
def unload (g : Geometry s) (x : FullArray s g.rows) :=
  ActivePrefixDirtyControlConjugationRun.result .uNegative s g.source g.rows (g.n*g.b) g.compactSuffix g.compactFits g.sourceVolume x

def early (g : Geometry s) (x : FullArray s g.rows) := negative g (correction g (pure g (selected g x)))
def later (g : Geometry s) (x : FullArray s g.rows) := unload g (early g (load g (early g x)))

theorem target_sources (d : Inputs s g) (x : FullArray s g.rows) :
    SharedBank.payload (caller d x) targetFocus=
      ActivePrefixDirtyControlLoadPlaced.sources (a := prime) (m := .selected) g.target g.rows g.targetSuffix
        d.ht d.rs d.bt (view g.targetVolume x) := by
  rw [←caller_view g.targetVolume d x]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem compact_sources (d : Inputs s g) (x : FullArray s g.rows) :
    SharedBank.payload (caller d x) compactFocus=
      ActivePrefixDirtyControlConjugationData.base d.gs d.bw d.hc d.rs d.bc x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem source_sources (d : Inputs s g) (x : FullArray s g.rows) :
    SharedBank.payload (caller d x) sourceFocus=
      ActivePrefixDirtyControlConjugationData.base d.gs d.bw d.hx d.rs d.bc x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceData
