import IntegerMultBounds.Machine.BinaryAddressOffsetData

/-! Physically build the source address table and the literal dummy-control
word used by the uniform gather. No complete table or repeated control stream
is part of the input contract. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetPrepare
open SharedPlacementAlphabet (setTape)
open BinaryAddressOffsetHeaders
open BinaryAddressOffsetData (source dummy)
noncomputable section

def sourceBank (hs : Fin 3 → List Bool) (q n : ℕ) :=
  setTape (BinaryAddressOffsetHeaders.output hs q n) 6
    (putWord (fun _ => blank) 0 ((source q n).map (bitSymbol (a := 0)))) 0

def output (hs : Fin 3 → List Bool) (q n : ℕ) :=
  setTape (sourceBank hs q n) 7 (binary (dummy q n)) 1

def tablePlace : Fin (9+7) ≃ Fin 16 where
  toFun := ![9,6,10,11,12,3,13,14,15,0,1,2,4,5,7,8]
  invFun := ![9,10,11,5,12,13,1,14,15,0,2,3,4,6,7,8]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def fillPlace : Fin (3+13) ≃ Fin 16 where
  toFun := ![7,9,5,0,1,2,3,4,6,8,10,11,12,13,14,15]
  invFun := ![3,4,5,6,7,2,8,0,9,1,10,11,12,13,14,15]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def tableProgram := Placement.placed BinaryAddressTable.program tablePlace
def fillProgram := Placement.placed BinaryAddressTableFill.program fillPlace
def program := seq (seq BinaryAddressOffsetHeaders.program tableProgram) fillProgram

theorem table_hoare (hs : Fin 3 → List Bool) (q n : ℕ) :
    HoareTime tableProgram (fun z => z=BinaryAddressOffsetHeaders.output hs q n)
      (fun z => z=sourceBank hs q n) (BinaryAddressTable.constant*((n*q+1)*2^(n*q))) := by
  have ha : Placement.active tablePlace (BinaryAddressOffsetHeaders.output hs q n)=
      BinaryAddressTable.input (widthBits q n) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := Placement.hoare_at (BinaryAddressTable.constructs (widthBits q n) (n*q)
    (DimensionProductDescriptor.bits_value n q) (DimensionProductDescriptor.bits_canonical n q))
    tablePlace (BinaryAddressOffsetHeaders.output hs q n) ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem fill_hoare (hs : Fin 3 → List Bool) (q n : ℕ) :
    HoareTime fillProgram (fun z => z=sourceBank hs q n)
      (fun z => z=output hs q n) (8*(n*2^(n*q))+7*(countBits q n).length+39) := by
  have ha : Placement.active fillPlace (sourceBank hs q n)=BinaryAddressTableFill.input (countBits q n) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := Placement.hoare_at (BinaryAddressTableFill.runs (countBits q n) (n*2^(n*q))
    (DimensionProductDescriptor.bits_value n (2^(n*q)))) fillPlace (sourceBank hs q n) ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def cost (q n : ℕ) := BinaryAddressOffsetHeaders.cost q n+
  BinaryAddressTable.constant*((n*q+1)*2^(n*q))+(8*(n*2^(n*q))+7*(countBits q n).length+39)+2

theorem constructs (hs : Fin 3 → List Bool) (q n : ℕ) (hq : 0 < q)
    (hvq : Counter.value (hs 0)=q) (hvn : Counter.value (hs 2)=n)
    (hcq : GrowingCounterData.Canonical (hs 0)) (hcn : GrowingCounterData.Canonical (hs 2)) :
    HoareTime program (fun z => z=bank hs) (fun z => z=output hs q n) (cost q n) := by
  have h0 := BinaryAddressOffsetHeaders.constructs hs q n hq hvq hvn hcq hcn
  have h1 := h0.seq (table_hoare hs q n)
  have h2 := h1.seq (fill_hoare hs q n)
  exact h2.consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.BinaryAddressOffsetPrepare
