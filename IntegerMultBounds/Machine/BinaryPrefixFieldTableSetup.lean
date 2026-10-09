import IntegerMultBounds.Machine.BinaryPrefixFieldTablePrimitives
import IntegerMultBounds.Machine.BinaryDescriptorInstall

/-! Only W/start/d are initially present. The power/count descriptor, zero,
second d descriptor, complete address table and dummy controls are constructed
physically in one shared clean workspace. -/
namespace IntegerMultBounds.Machine.BinaryPrefixFieldTableSetup
noncomputable section
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationHeadersCore (bank)
open RecursiveChildQuotientsConstant (bits)

def binary (xs : List Bool) := RadixZeroFill.encodedBinary (q := 0) xs

def base (hs : Fin 3 → List Bool) : Tapes 9 0 :=
  ⟨![1,1,1,0,0,0,0,0,0],![binary (hs 0),binary (hs 1),binary (hs 2),
    (fun _ => blank),(fun _ => blank),(fun _ => blank),(fun _ => blank),(fun _ => blank),(fun _ => blank)]⟩
def counted (hs : Fin 3 → List Bool) (W : ℕ) := setTape (base hs) 3 (binary (bits (2^W))) 1
def zeroed (hs : Fin 3 → List Bool) (W : ℕ) := setTape (counted hs W) 4 (binary (bits 0)) 1
def duplicated (hs : Fin 3 → List Bool) (W : ℕ) := setTape (zeroed hs W) 8 (binary (hs 2)) 1
def addressed (hs : Fin 3 → List Bool) (W : ℕ) := setTape (duplicated hs W) 5 (BinaryAddressTable.outputTape W) 0
def prepared (hs : Fin 3 → List Bool) (W : ℕ) := setTape (addressed hs W) 6
  (CountedCopyReuse.binary (BinaryPrefixFieldTableData.dummy W)) 1

def powerFocus : Fin 2 → Fin 9 := ![0,3]
def tableFocus : Fin 2 → Fin 9 := ![0,5]
def fillFocus : Fin 2 → Fin 9 := ![3,6]
def powerProgram := CompactGadgetReservationHeadersPowerRound.powerProgram (a := 0) powerFocus (by decide)
def zeroProgram := Placement.placed (RecursiveChildQuotientsConstant.program (a := 0) 0)
  (FiniteReturnStackAt.placement (4 : Fin 24))
def copyProgram := BinaryDescriptorInstall.program 0 (2 : Fin 24) 8 (by decide)
def tableProgram := BinaryPrefixFieldTablePrimitives.tableProgram tableFocus (by decide)
def fillProgram := BinaryPrefixFieldTablePrimitives.fillProgram fillFocus (by decide)
def program := seq (seq (seq (seq powerProgram zeroProgram) copyProgram) tableProgram) fillProgram

theorem power_runs (hs : Fin 3 → List Bool) (W : ℕ) (hw : Counter.value (hs 0)=W)
    (hc : GrowingCounterData.Canonical (hs 0)) :
    HoareTime powerProgram (fun v => v=bank (base hs)) (fun v => v=bank (counted hs W))
      (FixedBasePowerDescriptor.constant 2*2^W) :=
  CompactGadgetReservationHeadersPowerRound.power (base hs) powerFocus (by decide) (hs 0) W hw hc rfl rfl rfl rfl

theorem zero_runs (hs : Fin 3 → List Bool) (W : ℕ) :
    HoareTime zeroProgram (fun v => v=bank (counted hs W)) (fun v => v=bank (zeroed hs W)) 6 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := 0) 0)
    (FiniteReturnStackAt.placement (4 : Fin 24)) (bank (counted hs W)) (by
      rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ (by decide)
  rintro v ⟨small,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  change setTape ((counted hs W).append (SharedBank.empty 15 0)) (Fin.castAdd 15 4) _ _ = _
  rw [SharedPlacementAlphabet.setTape_append_left]
  rfl

theorem copy_runs (hs : Fin 3 → List Bool) (W : ℕ) :
    HoareTime copyProgram (fun v => v=bank (zeroed hs W)) (fun v => v=bank (duplicated hs W))
      (2*(hs 2).length+5) := by
  have h := BinaryDescriptorInstall.install_hoare (2 : Fin 24) 8 (by decide) (bank (zeroed hs W))
    (hs 2) rfl rfl rfl rfl
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v rfl
  change setTape ((zeroed hs W).append (SharedBank.empty 15 0)) (Fin.castAdd 15 8) _ _ = _
  rw [SharedPlacementAlphabet.setTape_append_left]
  rfl

theorem table_runs (hs : Fin 3 → List Bool) (W : ℕ) (hw : Counter.value (hs 0)=W)
    (hc : GrowingCounterData.Canonical (hs 0)) :
    HoareTime tableProgram (fun v => v=bank (duplicated hs W)) (fun v => v=bank (addressed hs W))
      (BinaryAddressTable.constant*((W+1)*2^W)) :=
  BinaryPrefixFieldTablePrimitives.table (duplicated hs W) tableFocus (by decide) (hs 0) W hw hc rfl rfl rfl rfl

theorem fill_runs (hs : Fin 3 → List Bool) (W : ℕ) :
    HoareTime fillProgram (fun v => v=bank (addressed hs W)) (fun v => v=bank (prepared hs W))
      (8*2^W+7*(bits (2^W)).length+39) :=
  BinaryPrefixFieldTablePrimitives.fill (addressed hs W) fillFocus (by decide) (bits (2^W)) (2^W)
    (RecursiveChildQuotientsConstant.bits_value _) rfl rfl rfl rfl

def cost (hs : Fin 3 → List Bool) (W : ℕ) :=
  FixedBasePowerDescriptor.constant 2*2^W+1+6+1+(2*(hs 2).length+5)+1+
    BinaryAddressTable.constant*((W+1)*2^W)+1+(8*2^W+7*(bits (2^W)).length+39)

theorem constructs (hs : Fin 3 → List Bool) (W : ℕ) (hw : Counter.value (hs 0)=W)
    (hc : GrowingCounterData.Canonical (hs 0)) :
    HoareTime program (fun v => v=bank (base hs)) (fun v => v=bank (prepared hs W)) (cost hs W) :=
  ((((power_runs hs W hw hc).seq (zero_runs hs W)).seq (copy_runs hs W)).seq (table_runs hs W hw hc)).seq
    (fill_runs hs W)

end
end IntegerMultBounds.Machine.BinaryPrefixFieldTableSetup
