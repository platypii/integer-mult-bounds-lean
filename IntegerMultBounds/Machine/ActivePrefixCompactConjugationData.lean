import IntegerMultBounds.Machine.ActivePrefixCompactSwapPlaced
import IntegerMultBounds.Machine.ActivePrefixCompactParityLoadPlaced
import IntegerMultBounds.Machine.ActivePrefixCompactNegativeLoadPlaced
import IntegerMultBounds.Machine.BinaryPackedOffsetData

/-! Common physical bank for compact swap/load/swap. The eight original swap
geometry words and ten load-input words are supplied canonically. In particular,
preparation of the load prefix/source coordinates from stage controls is a
separate obligation; no offset table or interchange descriptor is supplied. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactConjugationData
noncomputable section
open Networks.Shared50ModularControl (prime)
open ActivePrefixParityOnlyBank (Shape)
open SharedPlacementAlphabet (setTape)

inductive Kind | parity | negative deriving DecidableEq

def privateCount : Kind → ℕ | .parity => 60 | .negative => 75
def constant : Kind → ℕ
  | .parity => ActivePrefixCompactParityLoad.constant
  | .negative => ActivePrefixCompactNegativeLoad.constant
abbrev swapCount := ActivePrefixCompactSwapPlaced.count

def swapFocus : Fin 9 → Fin 19 := ![0,1,2,3,4,5,6,7,18]
def loadFocus : Fin 11 → Fin 19 := ![8,9,10,11,12,13,14,15,16,17,18]
theorem swap_injective : Function.Injective swapFocus := by decide
theorem load_injective : Function.Injective loadFocus := by decide

def base {m : ℕ} (gs : Fin 7 → List Bool) (b : List Bool)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : Fin m → Bool) : Tapes 19 prime :=
  ⟨fun i => if i.val<18 then 1 else 0,
    fun i => if h : i.val<7 then RadixZeroFill.encodedBinary (gs ⟨i.val,h⟩)
      else if i.val=7 then RadixZeroFill.encodedBinary b
      else if h : i.val<16 then RadixZeroFill.encodedBinary (hs ⟨i.val-8,by omega⟩)
      else if i.val=16 then RadixZeroFill.encodedBinary rs
      else if i.val=17 then RadixZeroFill.encodedBinary bs
      else ActiveTargetRotation.word x⟩

def view {m n : ℕ} (h : m=n) (x : Fin m → Bool) : Fin n → Bool :=
  fun i => x (Fin.cast h.symm i)

theorem word_view {m n : ℕ} (h : m=n) (x : Fin m → Bool) :
    ActiveTargetRotation.word (a := prime) (view h x)=ActiveTargetRotation.word x := by
  subst n
  rfl

theorem base_view {m n : ℕ} (h : m=n) (gs : Fin 7 → List Bool) (b : List Bool)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : Fin m → Bool) :
    base gs b hs rs bs (view h x)=base gs b hs rs bs x := by
  unfold base
  rw [word_view]

theorem base_set {m n : ℕ} (gs : Fin 7 → List Bool) (b : List Bool)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    setTape (base gs b hs rs bs x) 18 (ActiveTargetRotation.word y) 0=base gs b hs rs bs y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def loadResult (kind : Kind) (s : Shape) (rows B : ℕ)
    (x : ActivePrefixCompactParityLoadData.Array s rows B) : ActivePrefixCompactParityLoadData.Array s rows B :=
  match kind with
  | .parity => ActivePrefixCompactParityLoad.result s rows B x
  | .negative => ActivePrefixCompactNegativeLoad.result s rows B x

def loadSources (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : ActivePrefixCompactParityLoadData.Array s rows B) :=
  ActivePrefixCompactParityLoadPlaced.sources (a := prime) s rows B hs rs bs x

theorem negative_sources (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : ActivePrefixCompactParityLoadData.Array s rows B) :
    ActivePrefixCompactNegativeLoadPlaced.sources (a := prime) s rows B hs rs bs x=loadSources s rows B hs rs bs x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem swap_sources (s : CompactGadgetReservationShape.Shape) (rows w : ℕ)
    (gs : Fin 7 → List Bool) (b : List Bool) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : ActivePrefixCompactSwapData.Array s rows w) :
    SharedBank.payload (base gs b hs rs bs x) swapFocus=ActivePrefixCompactSwapPlaced.sources gs b x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem load_sources (s : Shape) (rows B : ℕ) (gs : Fin 7 → List Bool) (b : List Bool)
    (hs : Fin 8 → List Bool) (rs bs : List Bool) (x : ActivePrefixCompactParityLoadData.Array s rows B) :
    SharedBank.payload (base gs b hs rs bs x) loadFocus=loadSources s rows B hs rs bs x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixCompactConjugationData
