import IntegerMultBounds.Machine.ActivePrefixSelectedLoadPlaced
import IntegerMultBounds.Machine.ActivePrefixCorrectionLoadPlaced
import IntegerMultBounds.Machine.ActivePrefixCompactConjugationPlaced
import IntegerMultBounds.Machine.SharedBankFamily

/-! One literal original-array bank for the four active early payload actions.
Numeric stage headers are prepared inputs; no offset table is supplied. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequenceData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixLayoutGeometry CompactActiveTargetGeometry
open ActivePrefixCompactConjugationData (Kind view word_view)
open Networks.Shared50ModularControl (prime)

abbrev Array (s : Shape) (rows : ℕ) := Fin (rows*s.recordWidth) → Bool

def targetFocus : Fin 11 → Fin 28 := ![8,9,10,11,12,13,14,15,24,25,27]
def compactFocus : Fin 19 → Fin 28 := ![0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,24,26,27]
theorem target_injective : Function.Injective targetFocus := by decide
theorem compact_injective : Function.Injective compactFocus := by decide

def base {m : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool)
    (ht hc : Fin 8 → List Bool) (rs bt bc : List Bool) (x : Fin m → Bool) : Tapes 28 prime :=
  ⟨fun i => if i.val<27 then 1 else 0,
    fun i => if h : i.val<7 then RadixZeroFill.encodedBinary (gs ⟨i.val,h⟩)
      else if i.val=7 then RadixZeroFill.encodedBinary bw
      else if h : i.val<16 then RadixZeroFill.encodedBinary (ht ⟨i.val-8,by omega⟩)
      else if h : i.val<24 then RadixZeroFill.encodedBinary (hc ⟨i.val-16,by omega⟩)
      else if i.val=24 then RadixZeroFill.encodedBinary rs
      else if i.val=25 then RadixZeroFill.encodedBinary bt
      else if i.val=26 then RadixZeroFill.encodedBinary bc
      else ActiveTargetRotation.word x⟩

theorem base_set {m n : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool)
    (ht hc : Fin 8 → List Bool) (rs bt bc : List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    SharedPlacementAlphabet.setTape (base gs bw ht hc rs bt bc x) 27
      (ActiveTargetRotation.word y) 0=base gs bw ht hc rs bt bc y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem base_view {m n : ℕ} (h : m=n) (gs : Fin 7 → List Bool) (bw : List Bool)
    (ht hc : Fin 8 → List Bool) (rs bt bc : List Bool) (x : Fin m → Bool) :
    base gs bw ht hc rs bt bc (view h x)=base gs bw ht hc rs bt bc x := by
  unfold base
  rw [word_view]

theorem target_volume (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.before) (rows : ℕ) :
    ActivePrefixSelectedLoadData.volume (targetShape s p offset hfit) rows (targetSuffix s p.after)=
      rows*s.recordWidth := by
  change (rows*2^(targetWidth s p.before))*(2^(p.n*p.q)*targetSuffix s p.after)=_
  rw [←target_count s (p.n*p.b) p.before rows p.compactFits]
  exact CompactActiveTargetGeometry.target_volume s (p.n*p.b) (p.n*p.q) p.before p.after rows
    p.compactFits p.activeSize


theorem selected_sources (l : ActivePrefixSelectedOffsetBank.Shape) (rows B : ℕ)
    (gs : Fin 7 → List Bool) (bw : List Bool) (ht hc : Fin 8 → List Bool)
    (rs bt bc : List Bool) (x : ActivePrefixSelectedLoadData.Array l rows B) :
    SharedBank.payload (base gs bw ht hc rs bt bc x) targetFocus=
      ActivePrefixSelectedLoadPlaced.sources (a := prime) l rows B ht rs bt x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem correction_sources (l : ActivePrefixSelectedOffsetBank.Shape) (rows B : ℕ)
    (gs : Fin 7 → List Bool) (bw : List Bool) (ht hc : Fin 8 → List Bool)
    (rs bt bc : List Bool) (x : ActivePrefixCorrectionLoadData.Array l rows B) :
    SharedBank.payload (base gs bw ht hc rs bt bc x) targetFocus=
      ActivePrefixCorrectionLoadPlaced.sources (a := prime) l rows B ht rs bt x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem compact_sources {m : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool)
    (ht hc : Fin 8 → List Bool) (rs bt bc : List Bool) (x : Fin m → Bool) :
    SharedBank.payload (base gs bw ht hc rs bt bc x) compactFocus=
      ActivePrefixCompactConjugationData.base gs bw hc rs bc x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def selected (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.before) (rows : ℕ) (x : Array s rows) : Array s rows :=
  view (target_volume s p offset hfit rows)
    (ActivePrefixSelectedLoad.result (targetShape s p offset hfit) rows (targetSuffix s p.after)
      (view (target_volume s p offset hfit rows).symm x))
def correction (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.before) (rows : ℕ) (x : Array s rows) : Array s rows :=
  view (target_volume s p offset hfit rows)
    (ActivePrefixCorrectionLoad.result (targetShape s p offset hfit) rows (targetSuffix s p.after)
      (view (target_volume s p offset hfit rows).symm x))
def compact (kind : Kind) (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.before) (rows : ℕ) (x : Array s rows) : Array s rows :=
  view (ActivePrefixCompactSwapData.volume_eq s rows (p.n*p.b) p.compactFits)
    (ActivePrefixCompactConjugationRun.result kind s
      (ActivePrefixCompactConjugationLayout.shape .before s p offset hfit) rows (p.n*p.b)
      (compactSuffix s (p.n*p.b)) (ActivePrefixCompactConjugationLayout.alignment .before s p offset hfit rows)
      (view (ActivePrefixCompactSwapData.volume_eq s rows (p.n*p.b) p.compactFits).symm x))
def result (s : Shape) (p : Parameters s) (offset : ℕ)
    (hfit : offset+p.f*p.q≤p.before) (rows : ℕ) (x : Array s rows) : Array s rows :=
  compact .negative s p offset hfit rows
    (correction s p offset hfit rows (compact .parity s p offset hfit rows (selected s p offset hfit rows x)))
end
end IntegerMultBounds.Machine.ActivePrefixEarlySequenceData
