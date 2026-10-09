import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersLayout
import IntegerMultBounds.Machine.ActivePrefixEarlySequenceData

/-! Original caller bank for the four early loads. Twenty-two original numeric
words and the array are supplied; both ten-word consumer header banks start
blank. Each header producer physically copies its own row word. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalData
noncomputable section
open Networks.Shared50ModularControl (prime)
open ActivePrefixLayoutHeadersData (Inputs)

abbrev HeaderWords := Fin 10 → List Bool

def head : Option HeaderWords → ℤ | none => 0 | some _ => 1
def tape (v : Option HeaderWords) (i : Fin 10) : ℤ → Fin (prime+4) :=
  match v with | none => fun _ => blank | some hs => RadixZeroFill.encodedBinary (hs i)
def state {m : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 14 → List Bool)
    (ht hc : Option HeaderWords) (x : Fin m → Bool) : Tapes 43 prime :=
  ⟨fun i => if i.val<22 then 1 else if i.val=22 then 0 else if i.val<33 then head ht else head hc,
    fun i => if h : i.val<7 then RadixZeroFill.encodedBinary (gs ⟨i.val,h⟩)
      else if i.val=7 then RadixZeroFill.encodedBinary bw
      else if h : i.val<22 then RadixZeroFill.encodedBinary (hs ⟨i.val-8,by omega⟩)
      else if i.val=22 then ActiveTargetRotation.word x
      else if h : i.val<33 then tape ht ⟨i.val-23,by omega⟩
      else tape hc ⟨i.val-33,by omega⟩⟩

def targetWords (d : Inputs) := ActivePrefixLayoutHeadersEndpoint.words .target d
def compactWords (d : Inputs) := ActivePrefixLayoutHeadersEndpoint.words .compactBefore d

def targetFocus : Fin 24 → Fin 43 := ![8,9,10,11,12,13,14,15,16,17,18,19,20,21,23,24,25,26,27,28,29,30,31,32]
def compactFocus : Fin 24 → Fin 43 := ![8,9,10,11,12,13,14,15,16,17,18,19,20,21,33,34,35,36,37,38,39,40,41,42]
def sequenceFocus : Fin 28 → Fin 43 := ![0,1,2,3,4,5,6,7,23,24,25,26,27,28,29,30,33,34,35,36,37,38,39,40,31,32,42,22]
theorem target_injective : Function.Injective targetFocus := by decide
theorem compact_injective : Function.Injective compactFocus := by decide
theorem sequence_injective : Function.Injective sequenceFocus := by decide

variable {m : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 14 → List Bool) (x : Fin m → Bool)

def base := state gs bw hs none none x
def targetReady (d : Inputs) := state gs bw hs (some (targetWords d)) none x
def ready (d : Inputs) := state gs bw hs (some (targetWords d)) (some (compactWords d)) x

theorem state_set (ht hc : Option HeaderWords) {n : ℕ} (y : Fin n → Bool) :
    SharedPlacementAlphabet.setTape (state gs bw hs ht hc x) 22 (ActiveTargetRotation.word y) 0=
      state gs bw hs ht hc y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem target_sources : SharedBank.payload (base gs bw hs x) targetFocus=
    ActivePrefixLayoutHeadersPlaced.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem compact_sources (d : Inputs) : SharedBank.payload (targetReady gs bw hs x d) compactFocus=
    ActivePrefixLayoutHeadersPlaced.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem target_outputs (d : Inputs)
    (hv : ∀ i, Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (other : Option HeaderWords) :
    SharedBank.payload (state gs bw hs (some (targetWords d)) other x) targetFocus=
      ActivePrefixLayoutHeadersPlaced.outputs .target d := by
  rw [ActivePrefixLayoutHeadersEndpoint.canonical_originals d hs hv hc]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem compact_outputs (d : Inputs)
    (hv : ∀ i, Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    SharedBank.payload (ready gs bw hs x d) compactFocus=ActivePrefixLayoutHeadersPlaced.outputs .compactBefore d := by
  rw [ActivePrefixLayoutHeadersEndpoint.canonical_originals d hs hv hc]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem target_frame (ht ht' hc : Option HeaderWords) :
    SharedBank.strip (state gs bw hs ht hc x) targetFocus=SharedBank.strip (state gs bw hs ht' hc x) targetFocus := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [targetFocus,Fin.exists_fin_succ]
  all_goals rfl

theorem compact_frame (ht hc hc' : Option HeaderWords) :
    SharedBank.strip (state gs bw hs ht hc x) compactFocus=SharedBank.strip (state gs bw hs ht hc' x) compactFocus := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [compactFocus,Fin.exists_fin_succ]
  all_goals rfl

theorem sequence_sources (d : Inputs) : SharedBank.payload (ready gs bw hs x d) sequenceFocus=
    ActivePrefixEarlySequenceData.base gs bw
      (fun i => targetWords d (Fin.castAdd 2 i)) (fun i => compactWords d (Fin.castAdd 2 i))
      (targetWords d 8) (targetWords d 9) (compactWords d 9) x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem sequence_frame (d : Inputs) {n : ℕ} (y : Fin n → Bool) :
    SharedBank.strip (ready gs bw hs x d) sequenceFocus=SharedBank.strip (ready gs bw hs y d) sequenceFocus := by
  change SharedBank.strip (state gs bw hs _ _ x) sequenceFocus=SharedBank.strip (state gs bw hs _ _ y) sequenceFocus
  rw [←state_set gs bw hs x _ _ y]
  exact (CompactGadgetReservationPlacement.strip_set _ sequenceFocus 27 _ _).symm

/-- Extensional endpoint assembly only: execution is supplied separately by
the physical header producer and its cleanup theorem. -/
theorem installed_eq {t : ℕ} (before after : Tapes t prime) (focus : Fin 24 → Fin t)
    (out : Tapes 24 prime) (hp : SharedBank.payload after focus=out)
    (hf : SharedBank.strip before focus=SharedBank.strip after focus) :
    ActivePrefixLayoutHeadersPlaced.installed before focus out=after := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : ∃ j,focus j=i
  · have h := congrFun (congrArg Tapes.head hp) hi.choose
    simpa only [ActivePrefixLayoutHeadersPlaced.installed,hi,↓reduceDIte,SharedBank.payload,hi.choose_spec] using h.symm
  · have h := congrFun (congrArg Tapes.head hf) i
    simpa only [ActivePrefixLayoutHeadersPlaced.installed,hi,↓reduceDIte,SharedBank.strip,↓reduceIte] using h
  · have h := congrFun (congrArg Tapes.tape hp) hi.choose
    simpa only [ActivePrefixLayoutHeadersPlaced.installed,hi,↓reduceDIte,SharedBank.payload,hi.choose_spec] using h.symm
  · have h := congrFun (congrArg Tapes.tape hf) i
    simpa only [ActivePrefixLayoutHeadersPlaced.installed,hi,↓reduceDIte,SharedBank.strip,↓reduceIte] using h

end
end IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalData
