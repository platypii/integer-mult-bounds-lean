import IntegerMultBounds.Machine.CountedControlWordRepeat
import IntegerMultBounds.Machine.BinaryAddressOffsetPrepare

/-! Produce a regular temporary-address table and the actual repeated control
stream for the selected mask-shift load. Original headers are ordered b/q/n;
the original control word is retained on tape16. -/
namespace IntegerMultBounds.Machine.BinarySelectedOffsetPrepare
noncomputable section
open SharedPlacementAlphabet (setTape)
open BinaryAddressOffsetHeaders (rangeBits)
open BinaryAddressOffsetRepeatData (copies)

def controls (Z : List Bool) : Tapes 1 0 :=
  ⟨fun _ => 0,fun _ => putWord (fun _ => blank) 0 (Z.map bitSymbol)⟩
def input (hs : Fin 3 → List Bool) (Z : List Bool) :=
  (BinaryAddressOffsetHeaders.bank hs).append (controls Z)
def tableBank (hs : Fin 3 → List Bool) (Z : List Bool) (b n : ℕ) :=
  (BinaryAddressOffsetPrepare.sourceBank hs b n).append (controls Z)
def output (hs : Fin 3 → List Bool) (Z : List Bool) (b n : ℕ) :=
  setTape (tableBank hs Z b n) 7
    (putWord (fun _ => blank) 0 ((copies Z (2^(n*b))).map bitSymbol)) 0

def repeatPlace : Fin (4+13) ≃ Fin 17 where
  toFun := ![16,7,9,4,0,1,2,3,5,6,8,10,11,12,13,14,15]
  invFun := ![4,5,6,7,3,8,9,1,10,2,11,12,13,14,15,16,0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def tableProgram := extend (seq BinaryAddressOffsetHeaders.program BinaryAddressOffsetPrepare.tableProgram) 1
def repeatProgram := Placement.placed CountedControlWordRepeat.program repeatPlace
def program := seq tableProgram repeatProgram
def cost (b n : ℕ) (Z : List Bool) := BinaryAddressOffsetHeaders.cost b n+
  BinaryAddressTable.constant*((n*b+1)*2^(n*b))+2+
  (2^(n*b)*(3*Z.length+9)+7*(rangeBits b n).length+31)

theorem table_runs (hs : Fin 3 → List Bool) (Z : List Bool) (b n : ℕ) (hb : 0<b)
    (hvb : Counter.value (hs 0)=b) (hvn : Counter.value (hs 2)=n)
    (cb : GrowingCounterData.Canonical (hs 0)) (cn : GrowingCounterData.Canonical (hs 2)) :
    HoareTime tableProgram (fun z => z=input hs Z) (fun z => z=tableBank hs Z b n)
      (BinaryAddressOffsetHeaders.cost b n+BinaryAddressTable.constant*((n*b+1)*2^(n*b))+1) := by
  have h := hoare_extend_eq ((BinaryAddressOffsetHeaders.constructs hs b n hb hvb hvn cb cn).seq
    (BinaryAddressOffsetPrepare.table_hoare hs b n)) (controls Z)
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem repeat_runs (hs : Fin 3 → List Bool) (Z : List Bool) (b n : ℕ) :
    HoareTime repeatProgram (fun z => z=tableBank hs Z b n) (fun z => z=output hs Z b n)
      (2^(n*b)*(3*Z.length+9)+7*(rangeBits b n).length+31) := by
  have ha : Placement.active repeatPlace (tableBank hs Z b n)=
      CountedControlWordRepeat.input Z (fun _ => blank) 0 (rangeBits b n) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _
  have h := Placement.hoare_at (CountedControlWordRepeat.runs Z (fun _ => blank) 0
    (rangeBits b n) (2^(n*b)) (FixedBasePowerDescriptor.result_value 2 (n*b)) rfl)
    repeatPlace (tableBank hs Z b n) ha
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl | exact (CountedLoopReuseAlphabet.encoding_binary _).symm

/-- Neither the regular address table nor its repeated original controls are
supplied. Both are physically built, with all loop clocks erased and heads
restored, from b/q/n and one original control word. -/
theorem runs (hs : Fin 3 → List Bool) (Z : List Bool) (b n : ℕ) (hb : 0<b)
    (hvb : Counter.value (hs 0)=b) (hvn : Counter.value (hs 2)=n)
    (cb : GrowingCounterData.Canonical (hs 0)) (cn : GrowingCounterData.Canonical (hs 2)) :
    HoareTime program (fun z => z=input hs Z) (fun z => z=output hs Z b n) (cost b n Z) := by
  exact ((table_runs hs Z b n hb hvb hvn cb cn).seq (repeat_runs hs Z b n)).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)
end
end IntegerMultBounds.Machine.BinarySelectedOffsetPrepare
