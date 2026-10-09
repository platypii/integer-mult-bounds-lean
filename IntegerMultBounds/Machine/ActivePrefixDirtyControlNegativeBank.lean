import IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativeData
import IntegerMultBounds.Machine.ActivePrefixParityNegativeNegate

/-! Original descriptor bank for real dirty-U parity-XOR generation and
rowwise negation, with only compact width and prefix count synthesized. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativeBank
noncomputable section
open ActivePrefixDirtyControlData (Shape values offsetWord)
open ActivePrefixDirtyControlNegativeData
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def positiveFocus : Fin 7 → Fin 10 := ![0,1,2,3,4,5,6]
def powerFocus : Fin 2 → Fin 10 := ![0,9]
def widthFocus : Fin 3 → Fin 10 := ![4,5,8]
def negateFocus : Fin 4 → Fin 10 := ![6,7,8,9]

def base (hs : Fin 6 → List Bool) : Tapes 10 a :=
  (FixedHeaderBankCopy.headerBank hs).append (SharedBank.empty 4 a)
def positive (s : Shape .parity) (hs : Fin 6 → List Bool) :=
  ActivePrefixDirtyControlPlaced.result (base (a := a) hs) positiveFocus s
def powered (s : Shape .parity) (hs : Fin 6 → List Bool) :=
  setTape (positive (a := a) s hs) 9 (RadixZeroFill.encodedBinary (bits (2^s.W))) 1
def headers (s : Shape .parity) (hs : Fin 6 → List Bool) :=
  setTape (powered (a := a) s hs) 8 (RadixZeroFill.encodedBinary (bits (s.n*s.b))) 1
def negated (s : Shape .parity) (hs : Fin 6 → List Bool) :=
  ActivePrefixParityNegativeNegate.result (headers (a := a) s hs) negateFocus (negative s)
def widthCleared (s : Shape .parity) (hs : Fin 6 → List Bool) :=
  setTape (negated (a := a) s hs) 8 (fun _ => blank) 0
def output (s : Shape .parity) (hs : Fin 6 → List Bool) :=
  setTape (base (a := a) hs) 7 (ActivePrefixParityNegativeNegate.word (negative s)) 0

theorem positive_sources (hs : Fin 6 → List Bool) :
    SharedBank.payload (base (a := a) hs) positiveFocus=ActivePrefixDirtyControlPlaced.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem negate_sources (s : Shape .parity) (hs : Fin 6 → List Bool) :
    SharedBank.payload (headers (a := a) s hs) negateFocus=
      ActivePrefixParityNegativeNegate.sources (rows s).flatten (bits (s.n*s.b)) (bits (2^s.W)) := by
  rw [rows_flatten,ActivePrefixParityNegativeNegate.sources,ActivePrefixParityNegativeNegate.local_payload]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleared (s : Shape .parity) (hs : Fin 6 → List Bool) :
    setTape (widthCleared (a := a) s hs) 9 (fun _ => blank) 0=output s hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativeBank
