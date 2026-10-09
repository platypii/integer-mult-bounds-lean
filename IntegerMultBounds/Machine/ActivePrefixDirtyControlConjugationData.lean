import IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadPlaced
import IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativePureLoadPlaced
import IntegerMultBounds.Machine.ActivePrefixDirtyControlUSwapPlaced
import IntegerMultBounds.Machine.ActivePrefixCompactSwapPlaced

/-! Four concrete compact conjugations: pure/negative-XOR on T and
pure/negative-pure on U. Every operation acts on the unchanged full-array type. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationData
noncomputable section
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationShape (Shape)

inductive Kind | tPure | tNegative | uPure | uNegative deriving DecidableEq
abbrev LoadShape := ActivePrefixDirtyControlData.Shape .parity
abbrev LoadArray (l : LoadShape) (rows B : ℕ) := ActivePrefixDirtyControlLoadData.Array (m := .pure) l rows B
abbrev FullArray (s : Shape) (rows : ℕ) := Fin (rows*s.recordWidth) → Bool
abbrev swapCount := ActivePrefixCompactSwapPlaced.count

def swapFocus : Fin 9 → Fin 17 := ![0,1,2,3,4,5,6,7,16]
def loadFocus : Fin 9 → Fin 17 := ![8,9,10,11,12,13,14,15,16]
theorem swap_injective : Function.Injective swapFocus := by decide
theorem load_injective : Function.Injective loadFocus := by decide

def base {m : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 6 → List Bool)
    (rs bs : List Bool) (x : Fin m → Bool) : Tapes 17 prime :=
  ⟨fun i => if i.val<16 then 1 else 0,
    fun i => if h : i.val<7 then RadixZeroFill.encodedBinary (gs ⟨i.val,h⟩)
      else if i.val=7 then RadixZeroFill.encodedBinary bw
      else if h : i.val<14 then RadixZeroFill.encodedBinary (hs ⟨i.val-8,by omega⟩)
      else if i.val=14 then RadixZeroFill.encodedBinary rs
      else if i.val=15 then RadixZeroFill.encodedBinary bs
      else ActiveTargetRotation.word x⟩

def view {m n : ℕ} (h : m=n) (x : Fin m → Bool) : Fin n → Bool := fun i => x (Fin.cast h.symm i)
theorem word_view {m n : ℕ} (h : m=n) (x : Fin m → Bool) :
    ActiveTargetRotation.word (a := prime) (view h x)=ActiveTargetRotation.word x := by subst n; rfl
theorem base_view {m n : ℕ} (h : m=n) (gs : Fin 7 → List Bool) (bw : List Bool)
    (hs : Fin 6 → List Bool) (rs bs : List Bool) (x : Fin m → Bool) :
    base gs bw hs rs bs (view h x)=base gs bw hs rs bs x := by unfold base; rw [word_view]
theorem base_set {m n : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 6 → List Bool)
    (rs bs : List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    setTape (base gs bw hs rs bs x) 16 (ActiveTargetRotation.word y) 0=base gs bw hs rs bs y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def tSwap (s : Shape) (rows w : ℕ) (hw : w≤s.H) (x : FullArray s rows) : FullArray s rows :=
  view (ActivePrefixCompactSwapData.volume_eq s rows w hw)
    (RadixRangePadding.transpose (view (ActivePrefixCompactSwapData.volume_eq s rows w hw).symm x))
def uSwap (s : Shape) (rows w : ℕ) (hw : w≤s.H) (x : FullArray s rows) : FullArray s rows :=
  view (ActivePrefixDirtyControlUSwapData.volume_eq s rows w hw)
    (RadixRangePadding.transpose (view (ActivePrefixDirtyControlUSwapData.volume_eq s rows w hw).symm x))
def swapped (kind : Kind) (s : Shape) (rows w : ℕ) (hw : w≤s.H) (x : FullArray s rows) : FullArray s rows := match kind with
  | .tPure | .tNegative => tSwap s rows w hw x
  | .uPure | .uNegative => uSwap s rows w hw x

def loadResult (kind : Kind) (l : LoadShape) (rows B : ℕ) (x : LoadArray l rows B) : LoadArray l rows B := match kind with
  | .tPure | .uPure => ActivePrefixDirtyControlLoad.result (m := .pure) l rows B x
  | .tNegative => ActivePrefixDirtyControlLoad.result (m := .negative) l rows B x
  | .uNegative => ActivePrefixDirtyControlNegativePureLoad.result l rows B x

def loadSources (l : LoadShape) (rows B : ℕ) (hs : Fin 6 → List Bool) (rs bs : List Bool) (x : LoadArray l rows B) :=
  ActivePrefixDirtyControlLoadPlaced.sources (a := prime) (m := .pure) l rows B hs rs bs x

theorem load_sources (l : LoadShape) (rows B : ℕ) (gs : Fin 7 → List Bool) (bw : List Bool)
    (hs : Fin 6 → List Bool) (rs bs : List Bool) (x : LoadArray l rows B) :
    SharedBank.payload (base gs bw hs rs bs x) loadFocus=loadSources l rows B hs rs bs x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def swapCost (kind : Kind) (s : Shape) (rows w : ℕ) := match kind with
  | .tPure | .tNegative => ActivePrefixCompactSwapRun.cost s rows w
  | .uPure | .uNegative => ActivePrefixDirtyControlUSwapRun.cost s rows w

def loadConstant (kind : Kind) := match kind with
  | .uNegative => ActivePrefixDirtyControlNegativePureLoad.constant
  | _ => ActivePrefixDirtyControlLoad.constant

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationData
