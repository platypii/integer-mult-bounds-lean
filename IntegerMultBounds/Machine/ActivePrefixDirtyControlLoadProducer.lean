import IntegerMultBounds.Machine.ActivePrefixDirtyControlPureSemantics
import IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionPlaced
import IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePlaced

/-! The four real dirty-U offset producers share a fixed fifty-one-tape private
workspace. Modes are fixed finite-control choices, never supplied streams. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadProducer
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}

inductive Mode | selected | correction | pure | negative
  deriving DecidableEq

def sourceKind : Mode → BinaryVaryingOffsetGatherPlaced.Kind
  | .selected | .correction => .selected
  | .pure | .negative => .parity
abbrev Shape (m : Mode) := ActivePrefixDirtyControlData.Shape (sourceKind m)
def values {m : Mode} (s : Shape m) := ActivePrefixDirtyControlData.values s

def width {m : Mode} (s : Shape m) := ActivePrefixDirtyControlData.outputRowWidth s
def word {m : Mode} (s : Shape m) := match m with
  | .selected => ActivePrefixDirtyControlData.offsetWord s
  | .correction => ActivePrefixDirtyControlCorrectionData.word s
  | .pure => ActivePrefixDirtyControlPureBank.offsetWord s
  | .negative => ActivePrefixDirtyControlNegativeData.negative s
@[simp] theorem word_length {m : Mode} (s : Shape m) : (word s).length=2^s.W*width s := by
  cases m
  · exact ActivePrefixDirtyControlData.offset_length s
  · exact ActivePrefixDirtyControlCorrectionData.word_length s
  · exact ActivePrefixDirtyControlPureBank.offset_length s
  · exact ActivePrefixDirtyControlNegativeData.negative_length s

def code (m : Mode) (focus : Fin 7 → Fin t) (hf : Function.Injective focus) : Σ c, Program (t+51) c a :=
  match m with
  | .selected => ⟨_,extend (ActivePrefixDirtyControlPlaced.program .selected focus hf) 12⟩
  | .correction => ⟨_,extend (ActivePrefixDirtyControlCorrectionPlaced.program focus hf) 1⟩
  | .pure => ⟨_,extend (ActivePrefixDirtyControlPurePlaced.program focus hf) 12⟩
  | .negative => ⟨_,ActivePrefixDirtyControlNegativePlaced.program focus hf⟩
def program (m : Mode) (focus : Fin 7 → Fin t) (hf : Function.Injective focus) := (code (a := a) m focus hf).2

def sources (hs : Fin 6 → List Bool) : Tapes 7 a := ActivePrefixDirtyControlPlaced.sources hs
def result {m : Mode} (caller : Tapes t a) (focus : Fin 7 → Fin t) (s : Shape m) :=
  setTape caller (focus 6) (ActivePrefixOffsetStreamsCleanup.word (word s)) 0

def constant := ActivePrefixDirtyControl.constant+ActivePrefixDirtyControlCorrection.constant+ActivePrefixDirtyControlNegative.constant

theorem pad39 (v : Tapes t a) :
    (CleanSubbank.bank (s := 39) v).append (SharedBank.empty 12 a)=CleanSubbank.bank (s := 51) v := by
  rw [SharedBankRawCompose.bank_eq_raw,SharedBankFamily.raw_append v (by omega),SharedBankRawCompose.bank_eq_raw]
theorem pad50 (v : Tapes t a) :
    (CleanSubbank.bank (s := 50) v).append (SharedBank.empty 1 a)=CleanSubbank.bank (s := 51) v := by
  rw [SharedBankRawCompose.bank_eq_raw,SharedBankFamily.raw_append v (by omega),SharedBankRawCompose.bank_eq_raw]

theorem produces (m : Mode) (caller : Tapes t a) (focus : Fin 7 → Fin t) (hf : Function.Injective focus)
    (s : Shape m) (hs : Fin 6 → List Bool) (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program m focus hf) (fun v => v=CleanSubbank.bank (s := 51) caller)
      (fun v => v=CleanSubbank.bank (s := 51) (result caller focus s))
      (constant*ActivePrefixDirtyControl.volume s) := by
  cases m
  · have h := hoare_extend_eq (ActivePrefixDirtyControlPlaced.produces caller focus hf s hs hsrc hv hc) (SharedBank.empty 12 a)
    simp only [pad39] at h
    exact h.consequence (fun _ h => h) (fun _ h => h) (Nat.mul_le_mul_right _ (by unfold constant; omega))
  · have h := hoare_extend_eq (ActivePrefixDirtyControlCorrectionPlaced.produces caller focus hf s hs hsrc hv hc) (SharedBank.empty 1 a)
    simp only [pad50] at h
    exact h.consequence (fun _ h => h) (fun _ h => h) (Nat.mul_le_mul_right _ (by unfold constant; omega))
  · have h := hoare_extend_eq (ActivePrefixDirtyControlPurePlaced.produces caller focus hf s hs hsrc hv hc) (SharedBank.empty 12 a)
    simp only [pad39] at h
    exact h.consequence (fun _ h => h) (fun _ h => h) (Nat.mul_le_mul_right _ (by unfold constant; omega))
  · exact (ActivePrefixDirtyControlNegativePlaced.produces caller focus hf s hs hsrc hv hc).consequence
      (fun _ h => h) (fun _ h => h) (Nat.mul_le_mul_right _ (by unfold constant; omega))

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadProducer
