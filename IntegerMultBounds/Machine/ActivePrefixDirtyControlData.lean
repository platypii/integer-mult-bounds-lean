import IntegerMultBounds.Machine.ActivePrefixDirtyControlParityPlaced
import IntegerMultBounds.Machine.ActivePrefixSelectedOffsetData
import IntegerMultBounds.Machine.BinaryVaryingOffsetGatherPlaced
import IntegerMultBounds.Machine.BinaryPrefixFieldTablePlaced
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlacedCleanup

/-! Dirty compact U supplies exactly one parity bit per b-bit digit. Prefix
projection and actual block-parity extraction produce the entire control stream;
there is no extra source digit and no assumed q-stride source field. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlData
noncomputable section
open BinaryVaryingOffsetGatherPlaced (Kind sourceWidth outputWidth)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ} {k : Kind}

structure Shape (k : Kind) where
  W : ℕ
  startT : ℕ
  startU : ℕ
  q : ℕ
  b : ℕ
  n : ℕ
  tempFits : startT+n*sourceWidth k q b≤W
  controlFits : startU+n*b≤W
  hb : 1≤b
  hbq : b+1≤q

def values (s : Shape k) : Fin 6 → ℕ := ![s.W,s.startT,s.startU,s.q,s.b,s.n]
def tempWidth (s : Shape k) := s.n*sourceWidth k s.q s.b
def outputRowWidth (s : Shape k) := s.n*outputWidth k s.q s.b

theorem clockFits (s : Shape k) : s.startU+s.n≤s.W := by
  have h : s.n≤s.n*s.b := Nat.le_mul_of_pos_right s.n s.hb
  have := s.controlFits
  omega

def powerFocus : Fin 2 → Fin 15 := ![0,6]
def widthFocus : Fin 3 → Fin 15 := ![4,5,7]
def countFocus : Fin 3 → Fin 15 := ![6,5,8]
def wideFocus : Fin 3 → Fin 15 := ![3,5,9]
def widthSlot : Kind → Fin 15 | .selected => 7 | .control => 5 | .parity => 9
def tempFocus (k : Kind) : Fin 4 → Fin 15 := ![0,1,widthSlot k,10]
def sourceFocus : Fin 4 → Fin 15 := ![0,2,7,11]
def clockFocus : Fin 4 → Fin 15 := ![0,2,5,12]
def parityFocus : Fin 5 → Fin 15 := ![11,12,13,4,8]
def gatherFocus : Fin 6 → Fin 15 := ![3,4,8,10,13,14]
def derivedFocus : Fin 4 → Fin 15 := ![6,7,8,9]
theorem temp_injective : Function.Injective (tempFocus k) := by cases k <;> decide

def base (hs : Fin 6 → List Bool) : Tapes 15 a :=
  (FixedHeaderBankCopy.headerBank hs).append (SharedBank.empty 9 a)
def install (v : Tapes 15 a) (i : Fin 15) (n : ℕ) := setTape v i (RadixZeroFill.encodedBinary (bits n)) 1

def power (s : Shape k) (hs : Fin 6 → List Bool) := install (base (a := a) hs) 6 (2^s.W)
def narrow (s : Shape k) (hs : Fin 6 → List Bool) := install (power (a := a) s hs) 7 (s.n*s.b)
def counted (s : Shape k) (hs : Fin 6 → List Bool) := install (narrow (a := a) s hs) 8 (s.n*2^s.W)
def headers (s : Shape k) (hs : Fin 6 → List Bool) := install (counted (a := a) s hs) 9 (s.n*s.q)
def derivedWords (s : Shape k) : Fin 4 → List Bool :=
  ![bits (2^s.W),bits (s.n*s.b),bits (s.n*2^s.W),bits (s.n*s.q)]

def tempWord (s : Shape k) := BinaryPrefixFieldTableData.word s.W s.startT (tempWidth s) s.tempFits
def sourceWord (s : Shape k) := BinaryPrefixFieldTableData.word s.W s.startU (s.n*s.b) s.controlFits
def clockWord (s : Shape k) := BinaryPrefixFieldTableData.word s.W s.startU s.n (clockFits s)
def controlWord (s : Shape k) := CountedPackedParityRun.parities s.b (sourceWord s) (clockWord s).length

def offsetWord (s : Shape k) := match k with
  | .selected => BinaryVaryingSelectedOffsetGather.word s.q s.b s.hb s.hbq (tempWord s) (controlWord s)
  | .control => BinaryVaryingControlOffsetGather.word s.q s.b s.hb s.hbq (tempWord s) (controlWord s)
  | .parity => BinaryVaryingParityOffsetGather.word s.q s.b s.hb s.hbq (tempWord s) (controlWord s)

@[simp] theorem control_length (s : Shape k) : (controlWord s).length=2^s.W*s.n := by
  simp [controlWord,clockWord]
@[simp] theorem offset_length (s : Shape k) : (offsetWord s).length=2^s.W*outputRowWidth s := by
  cases k <;> simp [offsetWord,outputRowWidth,outputWidth,Nat.mul_assoc]

def tempReady (s : Shape k) (hs : Fin 6 → List Bool) :=
  BinaryPrefixFieldTablePlaced.result (headers (a := a) s hs) (tempFocus k) s.W s.startT (tempWidth s) s.tempFits
def sourceReady (s : Shape k) (hs : Fin 6 → List Bool) :=
  BinaryPrefixFieldTablePlaced.result (tempReady (a := a) s hs) sourceFocus s.W s.startU (s.n*s.b) s.controlFits
def clockReady (s : Shape k) (hs : Fin 6 → List Bool) :=
  BinaryPrefixFieldTablePlaced.result (sourceReady (a := a) s hs) clockFocus s.W s.startU s.n (clockFits s)
def controlReady (s : Shape k) (hs : Fin 6 → List Bool) :=
  ActivePrefixDirtyControlParityPlaced.result (clockReady (a := a) s hs) parityFocus s.b (sourceWord s) (clockWord s)
def gathered (s : Shape k) (hs : Fin 6 → List Bool) :=
  BinaryVaryingOffsetGatherPlaced.result k (controlReady (a := a) s hs) gatherFocus
    s.q s.b s.hb s.hbq (tempWord s) (controlWord s) 0 0 0

def tempWidthWord (s : Shape k) (hs : Fin 6 → List Bool) : List Bool :=
  match k with | .selected => bits (s.n*s.b) | .control => hs 5 | .parity => bits (s.n*s.q)
def tempHeaders (s : Shape k) (hs : Fin 6 → List Bool) : Fin 3 → List Bool := ![hs 0,hs 1,tempWidthWord s hs]
def sourceHeaders (s : Shape k) (hs : Fin 6 → List Bool) : Fin 3 → List Bool := ![hs 0,hs 2,bits (s.n*s.b)]
def clockHeaders (hs : Fin 6 → List Bool) : Fin 3 → List Bool := ![hs 0,hs 2,hs 5]
def parityHeaders (s : Shape k) (hs : Fin 6 → List Bool) : Fin 2 → List Bool := ![hs 4,bits (s.n*2^s.W)]
def gatherHeaders (s : Shape k) (hs : Fin 6 → List Bool) : Fin 3 → List Bool := ![hs 3,hs 4,bits (s.n*2^s.W)]

theorem temp_sources (s : Shape k) (hs : Fin 6 → List Bool) :
    SharedBank.payload (headers (a := a) s hs) (tempFocus k)=BinaryPrefixFieldTablePlaced.sources (tempHeaders s hs) := by
  cases k <;> apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem source_sources (s : Shape k) (hs : Fin 6 → List Bool) :
    SharedBank.payload (tempReady (a := a) s hs) sourceFocus=BinaryPrefixFieldTablePlaced.sources (sourceHeaders s hs) := by
  cases k <;> apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem clock_sources (s : Shape k) (hs : Fin 6 → List Bool) :
    SharedBank.payload (sourceReady (a := a) s hs) clockFocus=BinaryPrefixFieldTablePlaced.sources (clockHeaders hs) := by
  cases k <;> apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem parity_sources (s : Shape k) (hs : Fin 6 → List Bool) :
    SharedBank.payload (clockReady (a := a) s hs) parityFocus=
      ActivePrefixDirtyControlParityPlaced.sources (sourceWord s) (clockWord s) (parityHeaders s hs) := by
  cases k <;> apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlData
