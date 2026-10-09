import IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionData
import IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetSubtract

/-! Six original descriptors and five initially empty tapes suffice for the
correction's two real operands, output, and synthesized width/count headers. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionBank
noncomputable section
open ActivePrefixDirtyControlData (Shape values)
open ActivePrefixDirtyControlCorrectionData
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def selectedFocus : Fin 7 → Fin 11 := ![0,1,2,3,4,5,6]
def controlFocus : Fin 7 → Fin 11 := ![0,1,2,3,4,5,7]
def powerFocus : Fin 2 → Fin 11 := ![0,10]
def widthFocus : Fin 3 → Fin 11 := ![3,5,9]
def subtractFocus : Fin 5 → Fin 11 := ![7,6,8,9,10]

def base (hs : Fin 6 → List Bool) : Tapes 11 a :=
  (FixedHeaderBankCopy.headerBank hs).append (SharedBank.empty 5 a)
def selectedReady (s : Shape .selected) (hs : Fin 6 → List Bool) :=
  ActivePrefixDirtyControlPlaced.result (base (a := a) hs) selectedFocus s
def operands (s : Shape .selected) (hs : Fin 6 → List Bool) :=
  ActivePrefixDirtyControlPlaced.result (selectedReady (a := a) s hs) controlFocus (controlShape s)
def powered (s : Shape .selected) (hs : Fin 6 → List Bool) :=
  setTape (operands (a := a) s hs) 10 (RadixZeroFill.encodedBinary (bits (2^s.W))) 1
def headers (s : Shape .selected) (hs : Fin 6 → List Bool) :=
  setTape (powered (a := a) s hs) 9 (RadixZeroFill.encodedBinary (bits (s.n*s.q))) 1
def subtracted (s : Shape .selected) (hs : Fin 6 → List Bool) :=
  ActivePrefixCorrectionOffsetSubtract.output (headers (a := a) s hs) subtractFocus (word s)
def widthCleared (s : Shape .selected) (hs : Fin 6 → List Bool) :=
  setTape (subtracted (a := a) s hs) 9 (fun _ => blank) 0
def output (s : Shape .selected) (hs : Fin 6 → List Bool) :=
  setTape (base (a := a) hs) 8 (ActivePrefixCorrectionOffsetSubtract.word (word s)) 0

theorem selected_sources (hs : Fin 6 → List Bool) :
    SharedBank.payload (base (a := a) hs) selectedFocus=ActivePrefixDirtyControlPlaced.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem control_sources (s : Shape .selected) (hs : Fin 6 → List Bool) :
    SharedBank.payload (selectedReady (a := a) s hs) controlFocus=ActivePrefixDirtyControlPlaced.sources hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem subtract_sources (s : Shape .selected) (hs : Fin 6 → List Bool) :
    SharedBank.payload (headers (a := a) s hs) subtractFocus=
      ActivePrefixCorrectionOffsetSubtract.sources
        (BinaryCorrectionOffsetLoop.left (rows s)) (BinaryCorrectionOffsetLoop.right (rows s))
        (bits (s.n*s.q)) (bits (2^s.W)) := by
  rw [left_rows,right_rows]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleared (s : Shape .selected) (hs : Fin 6 → List Bool) :
    setTape (widthCleared (a := a) s hs) 10 (fun _ => blank) 0=output s hs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionBank
