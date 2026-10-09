import IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersGeometry
import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersEndpoint
import IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalPlaced

/-! Highest-bit action starts with the unchanged original fourteen words
and full array; its five pair descriptors and all work tapes begin blank. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalData
noncomputable section
open ActiveTargetHighestPairData (Geometry Array)
open ActiveTargetHighestLayoutHeadersData
open ActivePrefixLayoutHeadersData (Inputs)
open ActiveTargetHighestPairOriginalData (arrayTape)
open Networks.Shared50ModularControl (prime)
open RecursiveChildQuotientsConstant (bits)

def words (mode : Mode) (d : Inputs) : Fin 5 → List Bool := fun i => bits (values mode d i)
def base {m : ℕ} (hs : Fin 14 → List Bool) (x : Fin m → Bool) : Tapes 44 prime :=
  (ActivePrefixLayoutHeadersEndpoint.input hs).append (arrayTape x)
def prepared {m : ℕ} (mode : Mode) (d : Inputs) (x : Fin m → Bool) : Tapes 44 prime :=
  (ActiveRepairRankHeadersCommands.bank (finished mode d)).append (arrayTape x)
def count := 44+ActiveTargetHighestPairOriginalData.count
def bank (v : Tapes 44 prime) := CleanSubbank.bank (s := ActiveTargetHighestPairOriginalData.count) v

def focus : Fin 6 → Fin 44 := ![14,15,16,17,18,43]
theorem focus_injective : Function.Injective focus := by decide

theorem words_value (mode : Mode) (d : Inputs) : ∀ i,Counter.value (words mode d i)=values mode d i :=
  fun _ => RecursiveChildQuotientsConstant.bits_value _
theorem words_canonical (mode : Mode) (d : Inputs) : ∀ i,GrowingCounterData.Canonical (words mode d i) :=
  fun _ => RecursiveChildQuotientsConstant.bits_canonical _

theorem prepared_sources {m : ℕ} (mode : Mode) (d : Inputs) (x : Fin m → Bool) :
    SharedBank.payload (prepared mode d x) focus=ActiveTargetHighestPairOriginalPlaced.sources (words mode d) x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem base_set {m n : ℕ} (hs : Fin 14 → List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    SharedPlacementAlphabet.setTape (base hs x) 43 (ActiveTargetRotation.word y) 0=base hs y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem prepared_set {m n : ℕ} (mode : Mode) (d : Inputs) (x : Fin m → Bool) (y : Fin n → Bool) :
    SharedPlacementAlphabet.setTape (prepared mode d x) (focus 5) (ActiveTargetRotation.word y) 0=prepared mode d y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalData
