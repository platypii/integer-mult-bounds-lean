import IntegerMultBounds.Machine.BinaryAddressTable
import IntegerMultBounds.Machine.PlacedDescriptorConstruction

/-! Construct the actual total address width, complete binary range and total
selected-digit count from original q/b/n. Every product and power is a real
fixed-control tape computation; b is retained for the subsequent parity gather. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetHeaders
open SharedPlacementAlphabet (setTape)
noncomputable section

def widthBits (q n : ℕ) := DimensionProductDescriptor.bits n q
def rangeBits (q n : ℕ) := FixedBasePowerStep.bits 2 (n*q)
def countBits (q n : ℕ) := DimensionProductDescriptor.bits n (2^(n*q))
def binary (xs : List Bool) := RadixZeroFill.encodedBinary (q := 0) xs

def bank (hs : Fin 3 → List Bool) : Tapes 16 0 :=
  ⟨fun i => if i.val<3 then 1 else 0,
    fun i => if h : i.val<3 then binary (hs ⟨i.val,h⟩) else fun _ => blank⟩
def widthBank (hs : Fin 3 → List Bool) (q n : ℕ) := setTape (bank hs) 3 (binary (widthBits q n)) 1
def rangeBank (hs : Fin 3 → List Bool) (q n : ℕ) := setTape (widthBank hs q n) 4 (binary (rangeBits q n)) 1
def output (hs : Fin 3 → List Bool) (q n : ℕ) := setTape (rangeBank hs q n) 5 (binary (countBits q n)) 1

def widthPlace : Fin (6+10) ≃ Fin 16 where
  toFun := ![9,3,10,0,11,2,1,4,5,6,7,8,12,13,14,15]
  invFun := ![3,6,5,1,7,8,9,10,11,0,2,4,12,13,14,15]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def rangePlace : Fin (8+8) ≃ Fin 16 where
  toFun := ![9,10,11,12,13,4,14,3,0,1,2,5,6,7,8,15]
  invFun := ![8,9,10,7,5,11,12,13,14,0,1,2,3,4,6,15]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def countPlace : Fin (6+10) ≃ Fin 16 where
  toFun := ![9,5,10,4,11,2,0,1,3,6,7,8,12,13,14,15]
  invFun := ![6,7,5,8,3,1,9,10,11,0,2,4,12,13,14,15]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def widthProgram := Placement.placed (DimensionProductDescriptor.program (q := 0)) widthPlace
def rangeProgram := Placement.placed (FixedBasePowerDescriptor.program (q := 0) 2) rangePlace
def countProgram := Placement.placed (DimensionProductDescriptor.program (q := 0)) countPlace
def program := seq (seq widthProgram rangeProgram) countProgram

theorem width_hoare (hs : Fin 3 → List Bool) (q n : ℕ) (hq : 0 < q)
    (hvq : Counter.value (hs 0)=q) (hvn : Counter.value (hs 2)=n)
    (hcq : GrowingCounterData.Canonical (hs 0)) (hcn : GrowingCounterData.Canonical (hs 2)) :
    HoareTime widthProgram (fun z => z=bank hs) (fun z => z=widthBank hs q n) (53*(n*q)+28) := by
  have ha : Placement.active widthPlace (bank hs)=DimensionProductDescriptor.input (hs 0) (hs 2) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := Placement.hoare_at (DimensionProductDescriptor.construct_hoare (hs 0) (hs 2) n q hq hvq hvn hcq hcn)
    widthPlace (bank hs) ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem range_hoare (hs : Fin 3 → List Bool) (q n : ℕ) :
    HoareTime rangeProgram (fun z => z=widthBank hs q n) (fun z => z=rangeBank hs q n)
      (FixedBasePowerDescriptor.constant 2*2^(n*q)) := by
  have ha : Placement.active rangePlace (widthBank hs q n)=FixedBasePowerDescriptor.input (widthBits q n) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> first | rfl |
      exact CountedLoopReuseAlphabet.encoding_binary _
  have hh := PlacedDescriptorConstruction.power_hoare rangePlace (widthBank hs q n) 2 (n*q) (by decide)
    (widthBits q n) (DimensionProductDescriptor.bits_value n q) (DimensionProductDescriptor.bits_canonical n q) ha
  exact hh

theorem count_hoare (hs : Fin 3 → List Bool) (q n : ℕ)
    (hvn : Counter.value (hs 2)=n) (hcn : GrowingCounterData.Canonical (hs 2)) :
    HoareTime countProgram (fun z => z=rangeBank hs q n) (fun z => z=output hs q n)
      (53*(n*2^(n*q))+28) := by
  have ha : Placement.active countPlace (rangeBank hs q n)=DimensionProductDescriptor.input (rangeBits q n) (hs 2) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := Placement.hoare_at (DimensionProductDescriptor.construct_hoare (rangeBits q n) (hs 2) n (2^(n*q))
    (by positivity) (FixedBasePowerDescriptor.result_value 2 (n*q)) hvn
    (FixedBasePowerDescriptor.result_canonical 2 (n*q)) hcn) countPlace (rangeBank hs q n) ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def cost (q n : ℕ) := 53*(n*q)+FixedBasePowerDescriptor.constant 2*2^(n*q)+53*(n*2^(n*q))+58

theorem constructs (hs : Fin 3 → List Bool) (q n : ℕ) (hq : 0 < q)
    (hvq : Counter.value (hs 0)=q) (hvn : Counter.value (hs 2)=n)
    (hcq : GrowingCounterData.Canonical (hs 0)) (hcn : GrowingCounterData.Canonical (hs 2)) :
    HoareTime program (fun z => z=bank hs) (fun z => z=output hs q n) (cost q n) := by
  have hh := ((width_hoare hs q n hq hvq hvn hcq hcn).seq (range_hoare hs q n)).seq (count_hoare hs q n hvn hcn)
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.BinaryAddressOffsetHeaders
