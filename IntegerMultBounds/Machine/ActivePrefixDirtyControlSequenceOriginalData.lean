import IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersGeometry
import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceData

/-! Original caller bank for the four early loads. Twenty-two original numeric
words and the array are supplied; both ten-word consumer header banks start
blank. Each header producer physically copies its own row word. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalData
noncomputable section
open Networks.Shared50ModularControl (prime)
open ActivePrefixLayoutHeadersData (Inputs)

abbrev HeaderWords := Fin 10 → List Bool

def head : Option HeaderWords → ℤ | none => 0 | some _ => 1
def tape (v : Option HeaderWords) (i : Fin 10) : ℤ → Fin (prime+4) :=
  match v with | none => fun _ => blank | some hs => RadixZeroFill.encodedBinary (hs i)
def state {m : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 14 → List Bool)
    (ht hc hx : Option HeaderWords) (x : Fin m → Bool) : Tapes 53 prime :=
  ⟨fun i => if i.val<22 then 1 else if i.val=22 then 0 else if i.val<33 then head ht else if i.val<43 then head hc else head hx,
    fun i => if h : i.val<7 then RadixZeroFill.encodedBinary (gs ⟨i.val,h⟩)
      else if i.val=7 then RadixZeroFill.encodedBinary bw
      else if h : i.val<22 then RadixZeroFill.encodedBinary (hs ⟨i.val-8,by omega⟩)
      else if i.val=22 then ActiveTargetRotation.word x
      else if h : i.val<33 then tape ht ⟨i.val-23,by omega⟩
      else if h : i.val<43 then tape hc ⟨i.val-33,by omega⟩
      else tape hx ⟨i.val-43,by omega⟩⟩

def words (k : ActivePrefixDirtyControlHeadersData.Kind) (d : Inputs) := ActivePrefixDirtyControlHeadersEndpoint.words k d
def targetWords := words .target
def compactWords := words .compact
def sourceWords := words .source

def targetFocus : Fin 24 → Fin 53 := ![8,9,10,11,12,13,14,15,16,17,18,19,20,21,23,24,25,26,27,28,29,30,31,32]
def compactFocus : Fin 24 → Fin 53 := ![8,9,10,11,12,13,14,15,16,17,18,19,20,21,33,34,35,36,37,38,39,40,41,42]
def sourceFocus : Fin 24 → Fin 53 := ![8,9,10,11,12,13,14,15,16,17,18,19,20,21,43,44,45,46,47,48,49,50,51,52]
def sequenceFocus : Fin 30 → Fin 53 := ![0,1,2,3,4,5,6,7,23,24,25,26,27,28,33,34,35,36,37,38,43,44,45,46,47,48,31,32,42,22]
theorem target_injective : Function.Injective targetFocus := by decide
theorem compact_injective : Function.Injective compactFocus := by decide
theorem source_injective : Function.Injective sourceFocus := by decide
theorem sequence_injective : Function.Injective sequenceFocus := by decide

variable {m : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 14 → List Bool) (x : Fin m → Bool)
def base := state gs bw hs none none none x
def targetReady (d : Inputs) := state gs bw hs (some (targetWords d)) none none x
def compactReady (d : Inputs) := state gs bw hs (some (targetWords d)) (some (compactWords d)) none x
def ready (d : Inputs) := state gs bw hs (some (targetWords d)) (some (compactWords d)) (some (sourceWords d)) x

theorem state_set (ht hc hx : Option HeaderWords) {n : ℕ} (y : Fin n → Bool) :
    SharedPlacementAlphabet.setTape (state gs bw hs ht hc hx x) 22 (ActiveTargetRotation.word y) 0=
      state gs bw hs ht hc hx y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem target_sources (hc hx : Option HeaderWords) :
    SharedBank.payload (state gs bw hs none hc hx x) targetFocus=
      ActivePrefixDirtyControlHeadersPlaced.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem target_outputs (d : Inputs)
    (hv : ∀ i, Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc₀ : ∀ i, GrowingCounterData.Canonical (hs i)) (hc hx : Option HeaderWords) :
    SharedBank.payload (state gs bw hs (some (targetWords d)) hc hx x) targetFocus=
      ActivePrefixDirtyControlHeadersPlaced.outputs .target d := by
  rw [ActivePrefixLayoutHeadersEndpoint.canonical_originals d hs hv hc₀]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem target_frame (ht ht' hc hx : Option HeaderWords) :
    SharedBank.strip (state gs bw hs ht hc hx x) targetFocus=
      SharedBank.strip (state gs bw hs ht' hc hx x) targetFocus := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first
    | rw [ite_eq_left (by decide)] <;> rfl
    | rw [ite_eq_right (by decide)]; rfl

theorem compact_sources (ht hx : Option HeaderWords) :
    SharedBank.payload (state gs bw hs ht none hx x) compactFocus=
      ActivePrefixDirtyControlHeadersPlaced.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem compact_outputs (d : Inputs)
    (hv : ∀ i, Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc₀ : ∀ i, GrowingCounterData.Canonical (hs i)) (ht hx : Option HeaderWords) :
    SharedBank.payload (state gs bw hs ht (some (compactWords d)) hx x) compactFocus=
      ActivePrefixDirtyControlHeadersPlaced.outputs .compact d := by
  rw [ActivePrefixLayoutHeadersEndpoint.canonical_originals d hs hv hc₀]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem compact_frame (ht hc hc' hx : Option HeaderWords) :
    SharedBank.strip (state gs bw hs ht hc hx x) compactFocus=
      SharedBank.strip (state gs bw hs ht hc' hx x) compactFocus := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first
    | rw [ite_eq_left (by decide)] <;> rfl
    | rw [ite_eq_right (by decide)]; rfl

theorem source_sources (ht hc : Option HeaderWords) :
    SharedBank.payload (state gs bw hs ht hc none x) sourceFocus=
      ActivePrefixDirtyControlHeadersPlaced.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem source_outputs (d : Inputs)
    (hv : ∀ i, Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc₀ : ∀ i, GrowingCounterData.Canonical (hs i)) (ht hc : Option HeaderWords) :
    SharedBank.payload (state gs bw hs ht hc (some (sourceWords d)) x) sourceFocus=
      ActivePrefixDirtyControlHeadersPlaced.outputs .source d := by
  rw [ActivePrefixLayoutHeadersEndpoint.canonical_originals d hs hv hc₀]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem source_frame (ht hc hx hx' : Option HeaderWords) :
    SharedBank.strip (state gs bw hs ht hc hx x) sourceFocus=
      SharedBank.strip (state gs bw hs ht hc hx' x) sourceFocus := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first
    | rw [ite_eq_left (by decide)] <;> rfl
    | rw [ite_eq_right (by decide)]; rfl

theorem installed_eq {t : ℕ} (before after : Tapes t prime) (focus : Fin 24 → Fin t)
    (out : Tapes 24 prime) (hp : SharedBank.payload after focus=out)
    (hf : SharedBank.strip before focus=SharedBank.strip after focus) :
    ActivePrefixDirtyControlHeadersPlaced.installed before focus out=after := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : ∃ j,focus j=i
  · have h := congrFun (congrArg Tapes.head hp) hi.choose
    simpa only [ActivePrefixDirtyControlHeadersPlaced.installed,hi,↓reduceDIte,SharedBank.payload,hi.choose_spec] using h.symm
  · have h := congrFun (congrArg Tapes.head hf) i
    simpa only [ActivePrefixDirtyControlHeadersPlaced.installed,hi,↓reduceDIte,SharedBank.strip,↓reduceIte] using h
  · have h := congrFun (congrArg Tapes.tape hp) hi.choose
    simpa only [ActivePrefixDirtyControlHeadersPlaced.installed,hi,↓reduceDIte,SharedBank.payload,hi.choose_spec] using h.symm
  · have h := congrFun (congrArg Tapes.tape hf) i
    simpa only [ActivePrefixDirtyControlHeadersPlaced.installed,hi,↓reduceDIte,SharedBank.strip,↓reduceIte] using h

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalData
