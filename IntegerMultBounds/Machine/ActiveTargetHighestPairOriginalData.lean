import IntegerMultBounds.Machine.ActiveTargetHighestPairHeadersEndpoint
import IntegerMultBounds.Machine.ActiveTargetHighestPairPlaced

/-! The highest-pair machine starts with five original numeric words and the
unchanged full array. Ten headers and every native work tape begin blank. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalData
noncomputable section
open ActiveTargetHighestPairData
open ActiveTargetHighestPairHeadersData
open ActiveTargetHighestPairHeadersEndpoint
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)

def arrayTape {m : ℕ} (x : Fin m → Bool) : Tapes 1 prime := ⟨fun _ => 0,fun _ => ActiveTargetRotation.word x⟩
def base {m : ℕ} (hs : Fin 5 → List Bool) (x : Fin m → Bool) : Tapes 44 prime :=
  (ActiveTargetHighestPairHeadersEndpoint.input hs).append (arrayTape x)
def prepared {m : ℕ} (g : Geometry) (x : Fin m → Bool) : Tapes 44 prime :=
  (ActiveRepairRankHeadersCommands.bank (finished g)).append (arrayTape x)
def count := 44+ActiveTargetHighestPairRun.count
def bank (v : Tapes 44 prime) := CleanSubbank.bank (s := ActiveTargetHighestPairRun.count) v

def focus : Fin 11 → Fin 44 := ![5,6,7,8,9,10,11,12,13,14,43]
theorem focus_injective : Function.Injective focus := by decide

theorem prepared_sources {m : ℕ} (g : Geometry) (x : Fin m → Bool) :
    SharedBank.payload (prepared g x) focus=caller (words g) x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem base_set {m n : ℕ} (hs : Fin 5 → List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    setTape (base hs x) 43 (ActiveTargetRotation.word y) 0=base hs y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem prepared_set {m n : ℕ} (g : Geometry) (x : Fin m → Bool) (y : Fin n → Bool) :
    setTape (prepared g x) (focus 10) (ActiveTargetRotation.word y) 0=prepared g y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem bank_raw (v : Tapes 44 prime) : bank v=SharedBankStageInput.raw v count :=
  SharedBankRawCompose.bank_eq_raw v

end
end IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalData
