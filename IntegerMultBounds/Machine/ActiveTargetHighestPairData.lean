import IntegerMultBounds.Machine.ActivePrefixDirtyControlLoadPlaced
import IntegerMultBounds.Machine.BinaryPackedFieldSwap
import IntegerMultBounds.Machine.ActiveTargetHighestLaterValue

/-! Two literal one-bit fields in the original array with arbitrary outer
rows. Numeric coordinates are inputs; the actual pure offset producer reads
the earlier bit and all generated streams are physically erased. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairData
noncomputable section
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)

structure Geometry where
  L : ℕ
  G : ℕ
  K : ℕ
  rows : ℕ
  payload : ℕ
  positiveLeft : 1≤L
  positiveRows : 0<rows
  positivePayload : 0<payload

def W (g : Geometry) := g.L+1+g.G
def P (g : Geometry) := g.rows*2^g.L
def gap (g : Geometry) := 2^g.G
def suffix (g : Geometry) := 2^g.K*g.payload
def volume (g : Geometry) := RadixRangePadding.volume (P g) 2 (gap g) (suffix g)
abbrev Array (g : Geometry) := Fin (volume g) → Bool

def loadShape (g : Geometry) : ActivePrefixDirtyControlData.Shape .parity where
  W := W g
  startT := g.G
  startU := g.G
  q := 2
  b := 1
  n := 1
  tempFits := by change g.G+1*2≤W g; have := g.positiveLeft; unfold W; omega
  controlFits := by unfold W; omega
  hb := by decide
  hbq := by decide

theorem load_volume (g : Geometry) : volume g=ActivePrefixDirtyControlLoadData.volume (m := .pure)
    (loadShape g) g.rows (suffix g) := by
  change P g*2*gap g*2*suffix g=(g.rows*2^W g)*(2^1*suffix g)
  unfold P gap W
  simp only [pow_add,pow_one]
  ring

def values (g : Geometry) : Fin 10 → ℕ := ![W g,g.G,g.G,2,1,1,g.rows,suffix g,P g,gap g]
def loadHeaders (hs : Fin 10 → List Bool) : Fin 6 → List Bool := fun i => hs (Fin.castAdd 4 i)
def swapHeaders (hs : Fin 10 → List Bool) : Fin 4 → List Bool := ![hs 8,hs 9,hs 7,hs 4]
def loadFocus : Fin 9 → Fin 11 := ![0,1,2,3,4,5,6,7,10]
def swapFocus : Fin 4 → Fin 11 := ![8,9,7,4]
theorem load_injective : Function.Injective loadFocus := by decide
theorem swap_ne : ∀ i, swapFocus i≠(10 : Fin 11) := by decide

def caller {m : ℕ} (hs : Fin 10 → List Bool) (x : Fin m → Bool) : Tapes 11 prime :=
  ⟨fun i => if i.val<10 then 1 else 0,
    fun i => if h : i.val<10 then RadixZeroFill.encodedBinary (hs ⟨i.val,h⟩)
      else ActiveTargetRotation.word x⟩

theorem caller_set {m n : ℕ} (hs : Fin 10 → List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    setTape (caller hs x) 10 (ActiveTargetRotation.word y) 0=caller hs y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def view {m n : ℕ} (h : m=n) (x : Fin m → Bool) : Fin n → Bool := fun i => x (Fin.cast h.symm i)
theorem caller_view {m n : ℕ} (h : m=n) (hs : Fin 10 → List Bool) (x : Fin m → Bool) :
    caller hs (view h x)=caller hs x := by subst n; rfl

def result (g : Geometry) (x : Array g) : Array g :=
  view (load_volume g).symm (ActivePrefixDirtyControlLoad.result (m := .pure)
    (loadShape g) g.rows (suffix g) (view (load_volume g) x))
def later (g : Geometry) (x : Array g) :=
  RadixRangePadding.transpose (result g (RadixRangePadding.transpose x))

theorem load_sources (g : Geometry) (hs : Fin 10 → List Bool) (x : Array g) :
    SharedBank.payload (caller hs x) loadFocus=ActivePrefixDirtyControlLoadPlaced.sources (m := .pure)
      (loadShape g) g.rows (suffix g) (loadHeaders hs) (hs 6) (hs 7) (view (load_volume g) x) := by
  rw [←caller_view (load_volume g) hs x]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem load_values (g : Geometry) (hs : Fin 10 → List Bool) (hv : ∀ i,Counter.value (hs i)=values g i) :
    ∀ i,Counter.value (loadHeaders hs i)=ActivePrefixDirtyControlData.values (loadShape g) i := by
  intro i; fin_cases i <;> exact hv _

theorem swap_sources {m : ℕ} (hs : Fin 10 → List Bool) (x : Fin m → Bool) :
    BinaryAdjacentWidthHeadersShared.Sources (caller hs x) swapFocus (swapHeaders hs) := by
  constructor <;> intro i <;> fin_cases i <;> rfl

theorem swap_values (g : Geometry) (hs : Fin 10 → List Bool) (hv : ∀ i,Counter.value (hs i)=values g i) :
    ∀ i,Counter.value (swapHeaders hs i)=BinaryRadixRangePrepare.values (P g) (gap g) (suffix g) 1 i := by
  intro i; fin_cases i
  · exact hv 8
  · exact hv 9
  · exact hv 7
  · exact hv 4

end
end IntegerMultBounds.Machine.ActiveTargetHighestPairData
