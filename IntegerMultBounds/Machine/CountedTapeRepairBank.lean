import IntegerMultBounds.Machine.CountedRepairScanPrepare

/-! Literal input, output and charged costs for the uniform repair pipeline. -/
namespace IntegerMultBounds.Machine.CountedTapeRepairBank
noncomputable section
open IntegerMultBounds.Compact
open IntegerMultBounds.Compact.PowerTwo

abbrev Address (q b : ℕ) (Z : List Bool) := EarlyAddress (Bi b) (Li q) (controls Z).length
def width (q b : ℕ) (Z : List Bool) := Z.length*q+Z.length*b
def volume (q b : ℕ) (Z : List Bool) := (Z.length+1)*(q+b+1)
def keyCost (q b : ℕ) (Z : List Bool) := 5100*volume q b Z

def records (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  repairRecords (rankEquiv q b Z) (Sperm q b Z) data

def extracted (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  Compact.items (rankEquiv q b Z) (Sperm q b Z) (Tperm q b Z) (badSet q b Z) (width q b Z) data

def flagged (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  stream (rankEquiv q b Z) (badSet q b Z) (data ∘ (Sperm q b Z).symm)

def ideal (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  stream (rankEquiv q b Z) (badSet q b Z) (data ∘ (Tperm q b Z).symm)

def replacements (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  (sortedExtracted (rankEquiv q b Z) (Sperm q b Z) (Tperm q b Z) (badSet q b Z) (width q b Z) data).map Prod.snd

def input (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) :=
  CountedRepairScanPrepare.input (RepairScan.srcTape (records q b Z data)) Z hs

def prepared (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) :=
  CountedRepairScanPrepare.bank (width q b Z) (RepairScan.srcTape (records q b Z data)) Z hs

def output (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) : Tapes 42 1 :=
  ((RepairStage.stage (width q b Z)
    (TapeRadixSort.completed (width q b Z) (RepairStage.raw (extracted q b Z data)))
    (RepairStage.sortedRaw (width q b Z) (extracted q b Z data))
    (KeySelect.encode (RepairStage.sortedRaw (width q b Z) (extracted q b Z data))).length 0
    (RepairStage.encTape (Partition.encode (replacements q b Z data)))
    (Partition.encode (replacements q b Z data)).length
    (RepairStage.encTape (Partition.encode (flagged q b Z data)))
    (Partition.encode (flagged q b Z data)).length
    (RepairStage.encTape (Partition.encode (ideal q b Z data)))
    (Partition.encode (ideal q b Z data)).length).append
    (RepairScan.tail (records q b Z data) (width q b Z) (Mi q b Z))).append
    (CountedRepairKeyScan.scratch Z hs)

def scanCost (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  Mi q b Z*(keyCost q b Z+10)+3*(Partition.encode (flagged q b Z data)).length+
    (74*width q b Z+5)*(KeySelect.encode (RepairStage.raw (extracted q b Z data))).length+
    (2*width q b Z+3)*Nat.card {x // badSet q b Z x}+width q b Z+14

def cost (q b : ℕ) (Z : List Bool) (data : Address q b Z → List Bool) :=
  1004*volume q b Z+scanCost q b Z data+1

theorem output_ideal (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool) :
    (output q b Z hs data).tape 10=RepairStage.encTape (Partition.encode (ideal q b Z data)) := rfl

theorem output_scratch (q b : ℕ) (Z : List Bool) (hs : Fin 3 → List Bool) (data : Address q b Z → List Bool)
    (i : Fin 28) :
    (output q b Z hs data).tape (Fin.natAdd 14 i)=(CountedRepairKeyScan.scratch Z hs).tape i ∧
      (output q b Z hs data).head (Fin.natAdd 14 i)=(CountedRepairKeyScan.scratch Z hs).head i := by
  simp only [output,Tapes.append,Fin.addCases_right]
  exact ⟨trivial,trivial⟩

end
end IntegerMultBounds.Machine.CountedTapeRepairBank
