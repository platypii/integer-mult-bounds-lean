import IntegerMultBounds.Machine.ActivePrefixEarlySequenceData

/-! A fixed physical four-load early schedule on one unchanged original array.
All offset generation, swaps and erasure are real calls. Prepared numeric
stage headers are retained; their original-input synthesis remains separate. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequenceRun
noncomputable section
open ActivePrefixEarlySequenceData
open ActivePrefixLayoutShapes CompactActiveTargetGeometry
open CompactGadgetReservationShape (Shape)
open ActivePrefixCompactConjugationData (Kind view)
open Networks.Shared50ModularControl (prime)

abbrev parityCount := ActivePrefixCompactConjugationPlaced.count .parity
abbrev negativeCount := ActivePrefixCompactConjugationPlaced.count .negative
def count := 28+60+76+parityCount+negativeCount
theorem selected_le : 28+60≤count := by unfold count; omega
theorem correction_le : 28+76≤count := by unfold count; omega
theorem compact_le (kind : Kind) : 28+ActivePrefixCompactConjugationPlaced.count kind≤count := by
  cases kind <;> simp only [count,parityCount,negativeCount] <;> omega

def selectedProgram := SharedBankFamily.padProgram
  (ActivePrefixSelectedLoadPlaced.program (a := prime) targetFocus target_injective) selected_le
def correctionProgram := SharedBankFamily.padProgram
  (ActivePrefixCorrectionLoadPlaced.program (a := prime) targetFocus target_injective) correction_le
def compactProgram (kind : Kind) := SharedBankFamily.padProgram
  (ActivePrefixCompactConjugationPlaced.program kind compactFocus compact_injective) (compact_le kind)
def program := seq (seq (seq selectedProgram (compactProgram .parity)) correctionProgram)
  (compactProgram .negative)

structure Inputs (s : Shape) (p : Parameters s) (offset rows : ℕ)
    (hfit : offset+p.f*p.q≤p.before) where
  gs : Fin 7 → List Bool
  bw : List Bool
  ht : Fin 8 → List Bool
  hc : Fin 8 → List Bool
  rs : List Bool
  bt : List Bool
  bc : List Bool
  gv : ∀ i, Counter.value (gs i)=CompactGadgetReservationHeadersCarvedSchedule.originalValues s p.n rows i
  gc : ∀ i, GrowingCounterData.Canonical (gs i)
  gb : Counter.value bw=p.b
  cb : GrowingCounterData.Canonical bw
  tv : ∀ i, Counter.value (ht i)=ActivePrefixSelectedOffsetBank.values (targetShape s p offset hfit) i
  tc : ∀ i, GrowingCounterData.Canonical (ht i)
  cv : ∀ i, Counter.value (hc i)=ActivePrefixParityOnlyBank.values
    (ActivePrefixCompactConjugationLayout.shape .before s p offset hfit) i
  cc : ∀ i, GrowingCounterData.Canonical (hc i)
  rv : Counter.value rs=rows
  rc : GrowingCounterData.Canonical rs
  btv : Counter.value bt=targetSuffix s p.after
  btc : GrowingCounterData.Canonical bt
  bcv : Counter.value bc=compactSuffix s (p.n*p.b)
  bcc : GrowingCounterData.Canonical bc
  hr : 0<rows
  hK : 0<s.chunk
  hd : 0<s.axes
  hg : 0<s.guard
  hrecord : s.bits+1≤s.payload

variable {s : Shape} {p : Parameters s} {offset rows : ℕ} {hfit : offset+p.f*p.q≤p.before}

def caller (d : Inputs s p offset rows hfit) (x : Array s rows) :=
  base d.gs d.bw d.ht d.hc d.rs d.bt d.bc x

def selectedCost := ActivePrefixSelectedLoad.constant*(rows*s.recordWidth)
def correctionCost := ActivePrefixCorrectionLoad.constant*(rows*s.recordWidth)
def compactCost (kind : Kind) := ActivePrefixCompactConjugationRun.cost kind s rows (p.n*p.b)
def cost (s : Shape) (p : Parameters s) (rows : ℕ) :=
  ActivePrefixSelectedLoad.constant*(rows*s.recordWidth)+
    ActivePrefixCompactConjugationRun.cost .parity s rows (p.n*p.b)+
    ActivePrefixCorrectionLoad.constant*(rows*s.recordWidth)+
    ActivePrefixCompactConjugationRun.cost .negative s rows (p.n*p.b)+3

theorem selected_runs (d : Inputs s p offset rows hfit) (x : Array s rows) :
    HoareTime selectedProgram (fun v => v=SharedBankStageInput.raw (caller d x) count)
      (fun v => v=SharedBankStageInput.raw (caller d (selected s p offset hfit rows x)) count)
      (ActivePrefixSelectedLoad.constant*(rows*s.recordWidth)) := by
  let l := targetShape s p offset hfit
  let B := targetSuffix s p.after
  let y := view (ActivePrefixEarlySequenceData.target_volume s p offset hfit rows).symm x
  have hB : 0<B := by
    have hp : 0<s.payload := by have h := d.hrecord; omega
    dsimp [B,targetSuffix]
    positivity
  have hsrc : SharedBank.payload (caller d x) targetFocus=
      ActivePrefixSelectedLoadPlaced.sources (a := prime) l rows B d.ht d.rs d.bt y := by
    rw [caller,←base_view (ActivePrefixEarlySequenceData.target_volume s p offset hfit rows).symm d.gs d.bw d.ht d.hc d.rs d.bt d.bc x]
    exact selected_sources l rows B _ _ _ _ _ _ _ y
  have hh := ActivePrefixSelectedLoadPlaced.runs (caller d x) targetFocus target_injective
    l rows B d.hr hB (ActivePrefixLayoutAbsorption.target s p offset hfit d.hrecord)
    d.ht d.rs d.bt y hsrc d.tv d.tc d.rv d.rc d.btv d.btc
  have he : ActivePrefixSelectedLoadPlaced.result (caller d x) targetFocus l rows B y=
      caller d (selected s p offset hfit rows x) := by
    unfold ActivePrefixSelectedLoadPlaced.result caller selected
    change SharedPlacementAlphabet.setTape (base _ _ _ _ _ _ _ x) 27 _ 0=_
    rw [base_set]
    exact (base_view _ d.gs d.bw d.ht d.hc d.rs d.bt d.bc _).symm
  rw [he,ActivePrefixEarlySequenceData.target_volume] at hh
  exact SharedBankFamily.pad_clean_realizes selected_le _ _ _ hh

theorem correction_runs (d : Inputs s p offset rows hfit) (x : Array s rows) :
    HoareTime correctionProgram (fun v => v=SharedBankStageInput.raw (caller d x) count)
      (fun v => v=SharedBankStageInput.raw (caller d (correction s p offset hfit rows x)) count)
      (ActivePrefixCorrectionLoad.constant*(rows*s.recordWidth)) := by
  let l := targetShape s p offset hfit
  let B := targetSuffix s p.after
  let y := view (ActivePrefixEarlySequenceData.target_volume s p offset hfit rows).symm x
  have hB : 0<B := by
    have hp : 0<s.payload := by have h := d.hrecord; omega
    dsimp [B,targetSuffix]
    positivity
  have hsrc : SharedBank.payload (caller d x) targetFocus=
      ActivePrefixCorrectionLoadPlaced.sources (a := prime) l rows B d.ht d.rs d.bt y := by
    rw [caller,←base_view (ActivePrefixEarlySequenceData.target_volume s p offset hfit rows).symm d.gs d.bw d.ht d.hc d.rs d.bt d.bc x]
    exact correction_sources l rows B _ _ _ _ _ _ _ y
  have hh := ActivePrefixCorrectionLoadPlaced.runs (caller d x) targetFocus target_injective
    l rows B d.hr hB (ActivePrefixLayoutAbsorption.target s p offset hfit d.hrecord)
    d.ht d.rs d.bt y hsrc d.tv d.tc d.rv d.rc d.btv d.btc
  have he : ActivePrefixCorrectionLoadPlaced.result (caller d x) targetFocus l rows B y=
      caller d (correction s p offset hfit rows x) := by
    unfold ActivePrefixCorrectionLoadPlaced.result caller correction
    change SharedPlacementAlphabet.setTape (base _ _ _ _ _ _ _ x) 27 _ 0=_
    rw [base_set]
    exact (base_view _ d.gs d.bw d.ht d.hc d.rs d.bt d.bc _).symm
  rw [he] at hh
  have hv : ActivePrefixCorrectionLoadData.volume l rows B=rows*s.recordWidth :=
    ActivePrefixEarlySequenceData.target_volume s p offset hfit rows
  rw [hv] at hh
  exact SharedBankFamily.pad_clean_realizes correction_le _ _ _ hh

theorem compact_runs (kind : Kind) (d : Inputs s p offset rows hfit) (x : Array s rows) :
    HoareTime (compactProgram kind) (fun v => v=SharedBankStageInput.raw (caller d x) count)
      (fun v => v=SharedBankStageInput.raw (caller d (compact kind s p offset hfit rows x)) count)
      (ActivePrefixCompactConjugationRun.cost kind s rows (p.n*p.b)) := by
  let y := view (ActivePrefixCompactSwapData.volume_eq s rows (p.n*p.b) p.compactFits).symm x
  have hsrc : SharedBank.payload (caller d x) compactFocus=
      ActivePrefixCompactConjugationData.base d.gs d.bw d.hc d.rs d.bc y := by
    rw [caller,←base_view (ActivePrefixCompactSwapData.volume_eq s rows (p.n*p.b) p.compactFits).symm
      d.gs d.bw d.ht d.hc d.rs d.bt d.bc x]
    exact compact_sources _ _ _ _ _ _ _ y
  have hh := ActivePrefixCompactConjugationPlaced.runs kind .before (caller d x) compactFocus compact_injective
    s p offset hfit rows d.hr d.hK d.hd d.hg d.hrecord
    d.gs d.bw d.hc d.rs d.bc d.gv d.gc d.gb d.cb d.cv d.cc d.rv d.rc d.bcv d.bcc y hsrc
  have he : ActivePrefixCompactConjugationPlaced.result (caller d x) compactFocus
      (ActivePrefixCompactConjugationRun.result kind s
        (ActivePrefixCompactConjugationLayout.shape .before s p offset hfit) rows (p.n*p.b)
        (compactSuffix s (p.n*p.b)) (ActivePrefixCompactConjugationLayout.alignment .before s p offset hfit rows) y)=
      caller d (compact kind s p offset hfit rows x) := by
    unfold ActivePrefixCompactConjugationPlaced.result caller compact
    change SharedPlacementAlphabet.setTape (base _ _ _ _ _ _ _ x) 27 _ 0=_
    rw [base_set]
    exact (base_view _ d.gs d.bw d.ht d.hc d.rs d.bt d.bc _).symm
  simp only [ActivePrefixCompactConjugationLayout.suffix] at hh
  rw [he] at hh
  exact SharedBankFamily.pad_clean_realizes (compact_le kind) _ _ _ hh

/-- All four real payload actions run in the declared order on the same array,
with every private slot blank between calls and at the final endpoint. -/
theorem runs (d : Inputs s p offset rows hfit) (x : Array s rows) :
    HoareTime program (fun v => v=SharedBankStageInput.raw (caller d x) count)
      (fun v => v=SharedBankStageInput.raw (caller d (result s p offset hfit rows x)) count)
      (cost s p rows) := by
  have hh := (((selected_runs d x).seq
    (compact_runs .parity d (selected s p offset hfit rows x))).seq
    (correction_runs d (compact .parity s p offset hfit rows (selected s p offset hfit rows x)))).seq
    (compact_runs .negative d (correction s p offset hfit rows
      (compact .parity s p offset hfit rows (selected s p offset hfit rows x))))
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)
end
end IntegerMultBounds.Machine.ActivePrefixEarlySequenceRun
