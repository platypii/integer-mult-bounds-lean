import IntegerMultBounds.Machine.ActiveRepairEarlyKey
import IntegerMultBounds.Machine.RepairScan

/-! The actual fourteen-tape repair scan calls the current-address early key
machine. Every record uses its own genuine growing counter; controls are
parsed internally. Header synthesis and full permutation identification are
separate from this physical per-record scan contract. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyKeyScan
noncomputable section
open ActiveRepairEarlyKeyData ActiveRepairEarlyKeyData.Data
open ActiveRepairEarlyKeyRun

 def withCounter (d : Data) (cs : List Bool) : Data := {d with cs := cs}
 theorem valid_counter (d : Data) (h : Valid d) (cs : List Bool) : Valid (withCounter d cs) := by
  cases h
  constructor <;> assumption

def metadataPorts : Fin 30 → Fin 32 :=
  ![1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,31]
def focus : Fin 32 → Fin 44 :=
  ![13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,12,43]
theorem focus_injective : Function.Injective focus := by decide

def metadata (d : Data) : Tapes 30 1 := SharedBank.payload d.input metadataPorts
def scratch (d : Data) : Tapes 114 1 := (metadata d).append (SharedBank.empty 84 1)
def program := ActiveRepairEarlyKeyPlaced.program focus focus_injective

def flag (d : Data) (c j : ℕ) := (withCounter d (RepairScan.counter c j)).flag
def bits (d : Data) (c j : ℕ) := (withCounter d (RepairScan.counter c j)).destination

theorem bits_length (d : Data) (c j : ℕ) : (bits d c j).length=d.A :=
  ActiveRepairDestinationPatchRun.destination_length _ _ _ _ _ _ _ _

theorem metadata_counter (d : Data) (cs : List Bool) : metadata (withCounter d cs)=metadata d := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem scan_payload (d : Data) (c j : ℕ) (records : List Partition.Record) :
    SharedBank.payload
      ((RepairScan.scanBank d.A records (flag d c) (bits d c) c j [] j).append (metadata d)) focus=
      (withCounter d (RepairScan.counter c j)).input := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem padded_scan (d : Data) (c j : ℕ) (records : List Partition.Record) (key : List (Fin 5)) :
    CleanSubbank.bank (s := 84)
      ((RepairScan.scanBank d.A records (flag d c) (bits d c) c j key j).append (metadata d))=
      (RepairScan.scanBank d.A records (flag d c) (bits d c) c j key j).append (scratch d) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem written_scan (d : Data) (c j : ℕ) (records : List Partition.Record) :
    ActiveRepairEarlyKeyPlaced.result
      ((RepairScan.scanBank d.A records (flag d c) (bits d c) c j [] j).append (metadata d))
      focus (withCounter d (RepairScan.counter c j))=
      (RepairScan.scanBank d.A records (flag d c) (bits d c) c j
        (FlagCopy.keyWord (flag d c j) (bits d c j)) j).append (metadata d) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- A real reusable key routine for every record of the scan, with fixed
canonical field/patch descriptors but genuinely address-dependent controls. -/
theorem contract (d : Data) (h : Valid d) (c : ℕ) (records : List Partition.Record) :
    RepairScan.KeyContract d.A records (flag d c) (bits d c) c 114 program
      (29000*(d.A+1)) (scratch d) := by
  intro j _hj
  have hh := ActiveRepairEarlyKeyPlaced.runs
    ((RepairScan.scanBank d.A records (flag d c) (bits d c) c j [] j).append (metadata d))
    focus focus_injective (withCounter d (RepairScan.counter c j))
    (valid_counter d h _) (scan_payload d c j records)
  rw [written_scan,padded_scan,padded_scan] at hh
  exact hh

end
end IntegerMultBounds.Machine.ActiveRepairEarlyKeyScan
