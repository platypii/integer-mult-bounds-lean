import IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetSubtract
import IntegerMultBounds.Machine.ActivePrefixSelectedOffsetPlaced
import IntegerMultBounds.Machine.ActivePrefixControlOffsetPlaced
import IntegerMultBounds.Machine.ActivePrefixOffsetHeadersCleanup

/-! Eight immutable caller descriptors, two internally produced operands,
one correction output and five internally synthesized numeric descriptors. -/
namespace IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetBank
noncomputable section
open ActivePrefixSelectedOffsetBank (Shape values headerWords)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}

def selectedFocus : Fin 9 → Fin 16 := ![0,1,2,3,4,5,6,7,8]
def controlFocus : Fin 9 → Fin 16 := ![0,1,2,3,4,5,6,7,9]
def headerFocus : Fin 10 → Fin 16 := ![0,3,4,5,7,11,12,13,14,15]
def subtractFocus : Fin 5 → Fin 16 := ![9,8,10,15,11]
def cleanupFocus : Fin 5 → Fin 16 := ![11,12,13,14,15]
theorem selected_injective : Function.Injective selectedFocus := by decide
theorem control_injective : Function.Injective controlFocus := by decide
theorem header_injective : Function.Injective headerFocus := by decide
theorem subtract_injective : Function.Injective subtractFocus := by decide
theorem cleanup_injective : Function.Injective cleanupFocus := by decide

def base (hs : Fin 8 → List Bool) : Tapes 16 a :=
  (FixedHeaderBankCopy.headerBank hs).append (SharedBank.empty 8 a)
def selectedReady (s : Shape) (hs : Fin 8 → List Bool) :=
  ActivePrefixSelectedOffsetPlaced.result (base (a := a) hs) selectedFocus s
def operands (s : Shape) (hs : Fin 8 → List Bool) :=
  ActivePrefixControlOffsetPlaced.result (selectedReady (a := a) s hs) controlFocus s
def headers (s : Shape) (hs : Fin 8 → List Bool) :=
  ActivePrefixOffsetHeadersData.result (operands (a := a) s hs) headerFocus s.W s.q s.b s.n s.f
def subtracted (s : Shape) (hs : Fin 8 → List Bool) :=
  ActivePrefixCorrectionOffsetSubtract.output (headers (a := a) s hs) subtractFocus
    (ActivePrefixCorrectionOffsetData.word s)
def output (s : Shape) (hs : Fin 8 → List Bool) :=
  setTape (base (a := a) hs) 10 (ActivePrefixCorrectionOffsetSubtract.word (ActivePrefixCorrectionOffsetData.word s)) 0

theorem selected_sources (hs : Fin 8 → List Bool) :
    SharedBank.payload (base (a := a) hs) selectedFocus=ActivePrefixSelectedOffsetPlaced.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem control_sources (s : Shape) (hs : Fin 8 → List Bool) :
    SharedBank.payload (selectedReady (a := a) s hs) controlFocus=ActivePrefixControlOffsetPlaced.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem header_sources (s : Shape) (hs : Fin 8 → List Bool) :
    SharedBank.payload (operands (a := a) s hs) headerFocus=ActivePrefixOffsetHeadersData.sources (headerWords hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem subtract_sources (s : Shape) (hs : Fin 8 → List Bool) :
    SharedBank.payload (headers (a := a) s hs) subtractFocus=
      ActivePrefixCorrectionOffsetSubtract.sources
        (BinaryCorrectionOffsetLoop.left (ActivePrefixCorrectionOffsetData.rows s))
        (BinaryCorrectionOffsetLoop.right (ActivePrefixCorrectionOffsetData.rows s))
        (bits (s.n*s.q)) (bits (2^s.W)) := by
  rw [ActivePrefixCorrectionOffsetData.left_rows,ActivePrefixCorrectionOffsetData.right_rows]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleanup_tapes (s : Shape) (hs : Fin 8 → List Bool) :
    (∀ i, (subtracted (a := a) s hs).tape (cleanupFocus i)=
      RadixZeroFill.encodedBinary (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f i)) ∧
    (∀ i, (subtracted (a := a) s hs).head (cleanupFocus i)=1) := by
  constructor <;> intro i <;> fin_cases i <;> rfl

theorem cleared (s : Shape) (hs : Fin 8 → List Bool) :
    ActivePrefixOffsetHeadersCleanup.cleared (subtracted (a := a) s hs) cleanupFocus=output s hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetBank
