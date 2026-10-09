import IntegerMultBounds.Machine.ActiveRepairEarlyKeyScan

/-! Actual varying-address early scan, stable radix sort, prefix stripping
and reinsertion. These endpoints start with the physical scan bank prepared;
original header initialization, global ideal-permutation identification and
final working-tape cleanup remain separate. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyPipelineRun
noncomputable section
open ActiveRepairEarlyKeyData ActiveRepairEarlyKeyRun
open ActiveRepairEarlyKeyScan

def program := RepairScan.program 114 ActiveRepairEarlyKeyScan.program

def input (d : Data) (c : ℕ) (records : List Partition.Record) :=
  (RepairScan.scanBank d.A records (flag d c) (bits d c) c 0 [] 0).append (scratch d)
def output (d : Data) (c : ℕ) (records : List Partition.Record) :=
  ((RepairScan.finalStage d.A (RepairScan.items (flag d c) (bits d c) 0 records)
    (RepairScan.flagged (flag d c) 0 records)).append
    (RepairScan.tail records c records.length)).append (scratch d)

def extracted (d : Data) (c : ℕ) (records : List Partition.Record) :=
  KeySelect.encode (RepairStage.raw (RepairScan.items (flag d c) (bits d c) 0 records))
def holes (d : Data) (c : ℕ) (records : List Partition.Record) :=
  Reinsert.holes (RepairScan.flagged (flag d c) 0 records)
def cost (d : Data) (c : ℕ) (records : List Partition.Record) :=
  records.length*(29000*(d.A+1)+10)+3*(DropFlag.encode records).length+
    (74*d.A+5)*(extracted d c records).length+(2*d.A+3)*holes d c records+d.A+14

/-- This is one actual fixed complete scan/sort/strip/reinsert program; it
computes the flag and full destination from each genuine current scan rank. -/
theorem runs (d : Data) (h : Valid d) (c : ℕ) (records : List Partition.Record) :
    HoareTime program (fun z => z=input d c records) (fun z => z=output d c records)
      (cost d c records) := by
  have hbits : ∀ j < records.length, (bits d c j).length=d.A := fun j _ => bits_length d c j
  have hh := RepairScan.program_hoare d.A records (flag d c) (bits d c) c 114
    ActiveRepairEarlyKeyScan.program (29000*(d.A+1)) (scratch d) (contract d h c records) hbits
  exact hh.consequence (fun _ h => h) (fun _ h => h)
    (RepairScan.program_cost_le d.A records (flag d c) (bits d c) c (29000*(d.A+1)) hbits)

/-- Exact literal output stream, before the separately paid final tape cleanup. -/
theorem output_tape (d : Data) (c : ℕ) (records : List Partition.Record) :
    (output d c records).tape 10=RepairStage.encTape
      (Partition.encode (Reinsert.fill (RepairScan.flagged (flag d c) 0 records)
        (RepairStage.replacements d.A (RepairScan.items (flag d c) (bits d c) 0 records)))) := rfl

end
end IntegerMultBounds.Machine.ActiveRepairEarlyPipelineRun
