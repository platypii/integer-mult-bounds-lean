import IntegerMultBounds.Machine.ActivePrefixParityNegativeData
import IntegerMultBounds.Machine.ActivePrefixParityNegativeNegate
import IntegerMultBounds.Machine.ActivePrefixParityOffsetPlaced
import IntegerMultBounds.Machine.ActivePrefixOffsetHeadersCleanup

/-! Original eight descriptors, a consumed positive stream, the final negative
stream and five genuinely synthesized headers share one permanent caller bank. -/
namespace IntegerMultBounds.Machine.ActivePrefixParityNegativeBank
noncomputable section
open ActivePrefixParityOffsetBank (Shape values)
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}

def base (hs : Fin 8 → List Bool) : Tapes 15 a :=
  (FixedHeaderBankCopy.headerBank hs).append (SharedBank.empty 7 a)
def positiveFocus : Fin 9 → Fin 15 := ![0,1,2,3,4,5,6,7,8]
def headerFocus : Fin 10 → Fin 15 := ![0,3,4,5,7,10,11,12,13,14]
def negateFocus : Fin 4 → Fin 15 := ![8,9,12,10]
theorem positive_injective : Function.Injective positiveFocus := by decide
theorem header_injective : Function.Injective headerFocus := by decide
theorem negate_injective : Function.Injective negateFocus := by decide

def positive (s : Shape) (hs : Fin 8 → List Bool) :=
  ActivePrefixParityOffsetPlaced.result (base (a := a) hs) positiveFocus s
def headers (s : Shape) (hs : Fin 8 → List Bool) :=
  ActivePrefixOffsetHeadersData.result (positive (a := a) s hs) headerFocus s.W s.q s.b s.n s.f
def negated (s : Shape) (hs : Fin 8 → List Bool) :=
  ActivePrefixParityNegativeNegate.result (headers (a := a) s hs) negateFocus
    (ActivePrefixParityNegativeData.negative s)
def output (s : Shape) (hs : Fin 8 → List Bool) :=
  ActivePrefixOffsetHeadersCleanup.cleared (negated (a := a) s hs)
    (ActivePrefixOffsetHeadersData.outputFocus headerFocus)

def originalWords (hs : Fin 8 → List Bool) : Fin 5 → List Bool := ![hs 0,hs 3,hs 4,hs 5,hs 7]
def widthWord (s : Shape) := RecursiveChildQuotientsConstant.bits (s.n*s.b)
def countWord (s : Shape) := RecursiveChildQuotientsConstant.bits (2^s.W)

theorem positive_sources (hs : Fin 8 → List Bool) :
    SharedBank.payload (base (a := a) hs) positiveFocus=ActivePrefixParityOffsetPlaced.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem header_sources (s : Shape) (hs : Fin 8 → List Bool) :
    SharedBank.payload (positive (a := a) s hs) headerFocus=
      ActivePrefixOffsetHeadersData.sources (originalWords hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem negate_sources (s : Shape) (hs : Fin 8 → List Bool) :
    SharedBank.payload (headers (a := a) s hs) negateFocus=
      ActivePrefixParityNegativeNegate.sources (ActivePrefixParityNegativeData.rows s).flatten
        (widthWord s) (countWord s) := by
  rw [ActivePrefixParityNegativeNegate.sources,ActivePrefixParityNegativeNegate.local_payload,
    ActivePrefixParityNegativeData.rows_flatten]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem retained_headers (s : Shape) (hs : Fin 8 → List Bool) :
    (∀ i, (negated (a := a) s hs).tape (ActivePrefixOffsetHeadersData.outputFocus headerFocus i)=
      RadixZeroFill.encodedBinary (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f i)) ∧
    (∀ i, (negated (a := a) s hs).head (ActivePrefixOffsetHeadersData.outputFocus headerFocus i)=1) := by
  constructor <;> intro i <;> fin_cases i <;> rfl

theorem output_eq (s : Shape) (hs : Fin 8 → List Bool) :
    output (a := a) s hs=setTape (base hs) 9
      (ActivePrefixParityNegativeNegate.word (ActivePrefixParityNegativeData.negative s)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixParityNegativeBank
