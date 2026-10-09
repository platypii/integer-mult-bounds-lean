import IntegerMultBounds.Machine.ActiveRepairEarlyKeyOriginal
import IntegerMultBounds.Machine.RepairScan

/-! Every physical scan record generates its own field headers, parses its
genuine growing original rank, writes the full early key, and erases headers.
No parser or destination descriptor is part of the initial metadata bank. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyOriginalScan
noncomputable section
open ActiveRepairEarlyKeyOriginalData ActiveRepairEarlyKeyOriginalValid

def withCounter (d : Data) (cs : List Bool) : Data := {d with cs := cs}
theorem valid_counter (d : Data) (h : Valid d) (cs : List Bool) : Valid (withCounter d cs) := by
  cases h
  constructor <;> assumption

def metadataPorts : Fin 40 → Fin 42 :=
  ![1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,
    31,32,33,34,35,36,37,38,39,40,41]
def focus : Fin 42 → Fin 54 :=
  ![13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,
    39,40,41,42,12,43,44,45,46,47,48,49,50,51,52,53]
theorem focus_injective : Function.Injective focus := by decide

def metadata (d : Data) : Tapes 40 1 := SharedBank.payload d.input metadataPorts
def scratch (d : Data) : Tapes 166 1 := (metadata d).append (SharedBank.empty 126 1)
def program (side : ActiveRepairRankHeadersData.SourceSide) :=
  ActiveRepairEarlyKeyOriginalPlaced.program side focus focus_injective

def flag (d : Data) (c j : ℕ) := (withCounter d (RepairScan.counter c j)).key.flag
def bits (d : Data) (c j : ℕ) := (withCounter d (RepairScan.counter c j)).key.destination

theorem bits_length (d : Data) (c j : ℕ) : (bits d c j).length=d.geom.addressBits :=
  ActiveRepairDestinationPatchRun.destination_length _ _ _ _ _ _ _ _

theorem scan_payload (d : Data) (c j : ℕ) (records : List Partition.Record) :
    SharedBank.payload
      ((RepairScan.scanBank d.geom.addressBits records (flag d c) (bits d c) c j [] j).append
        (metadata d)) focus=(withCounter d (RepairScan.counter c j)).input := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem padded_scan (d : Data) (c j : ℕ) (records : List Partition.Record) (key : List (Fin 5)) :
    CleanSubbank.bank (s := 126)
      ((RepairScan.scanBank d.geom.addressBits records (flag d c) (bits d c) c j key j).append
        (metadata d))=
      (RepairScan.scanBank d.geom.addressBits records (flag d c) (bits d c) c j key j).append
        (scratch d) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem written_scan (d : Data) (c j : ℕ) (records : List Partition.Record) :
    ActiveRepairEarlyKeyOriginalPlaced.result
      ((RepairScan.scanBank d.geom.addressBits records (flag d c) (bits d c) c j [] j).append
        (metadata d)) focus (withCounter d (RepairScan.counter c j))=
      (RepairScan.scanBank d.geom.addressBits records (flag d c) (bits d c) c j
        (FlagCopy.keyWord (flag d c j) (bits d c j)) j).append (metadata d) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Actual original-input key generation at each growing scan rank. -/
theorem contract (d : Data) (h : Valid d) (c : ℕ) (records : List Partition.Record) :
    RepairScan.KeyContract d.geom.addressBits records (flag d c) (bits d c) c 166
      (program d.side) (ActiveRepairEarlyKeyOriginalRun.constant*(d.geom.addressBits+1))
      (scratch d) := by
  intro j _hj
  have hh := ActiveRepairEarlyKeyOriginalPlaced.runs
    ((RepairScan.scanBank d.geom.addressBits records (flag d c) (bits d c) c j [] j).append
      (metadata d)) focus focus_injective (withCounter d (RepairScan.counter c j))
    (valid_counter d h _) (scan_payload d c j records)
  rw [written_scan,padded_scan,padded_scan] at hh
  exact hh

end
end IntegerMultBounds.Machine.ActiveRepairEarlyOriginalScan
