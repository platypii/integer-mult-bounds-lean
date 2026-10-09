import IntegerMultBounds.Machine.ActiveRepairEarlyOriginalScan

/-! Physical original-input early repair: scan, stable key radix sort,
prefix stripping, and exact payload reinsertion. Per-record synthesized
metadata and all private key workspace are erased within the stated cost. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineRun
noncomputable section
open ActiveRepairEarlyKeyOriginalData ActiveRepairEarlyKeyOriginalValid
open ActiveRepairEarlyOriginalScan

def program (side : ActiveRepairRankHeadersData.SourceSide) :=
  RepairScan.program 166 (ActiveRepairEarlyOriginalScan.program side)

def input (d : Data) (c : ℕ) (records : List Partition.Record) :=
  (RepairScan.scanBank d.geom.addressBits records (flag d c) (bits d c) c 0 [] 0).append (scratch d)
def output (d : Data) (c : ℕ) (records : List Partition.Record) :=
  ((RepairScan.finalStage d.geom.addressBits
    (RepairScan.items (flag d c) (bits d c) 0 records) (RepairScan.flagged (flag d c) 0 records)).append
    (RepairScan.tail records c records.length)).append (scratch d)

def extracted (d : Data) (c : ℕ) (records : List Partition.Record) :=
  KeySelect.encode (RepairStage.raw (RepairScan.items (flag d c) (bits d c) 0 records))
def holes (d : Data) (c : ℕ) (records : List Partition.Record) :=
  Reinsert.holes (RepairScan.flagged (flag d c) 0 records)
def cost (d : Data) (c : ℕ) (records : List Partition.Record) :=
  records.length*(ActiveRepairEarlyKeyOriginalRun.constant*(d.geom.addressBits+1)+10)+
    3*(DropFlag.encode records).length+
    (74*d.geom.addressBits+5)*(extracted d c records).length+
    (2*d.geom.addressBits+3)*holes d c records+d.geom.addressBits+14

theorem runs (d : Data) (h : Valid d) (c : ℕ) (records : List Partition.Record) :
    HoareTime (program d.side) (fun z => z=input d c records) (fun z => z=output d c records)
      (cost d c records) := by
  have hbits : ∀ j < records.length, (bits d c j).length=d.geom.addressBits := fun j _ => bits_length d c j
  have hh := RepairScan.program_hoare d.geom.addressBits records (flag d c) (bits d c) c 166
    (ActiveRepairEarlyOriginalScan.program d.side)
    (ActiveRepairEarlyKeyOriginalRun.constant*(d.geom.addressBits+1)) (scratch d)
    (contract d h c records) hbits
  exact hh.consequence (fun _ h => h) (fun _ h => h)
    (RepairScan.program_cost_le d.geom.addressBits records (flag d c) (bits d c) c
      (ActiveRepairEarlyKeyOriginalRun.constant*(d.geom.addressBits+1)) hbits)

theorem output_tape (d : Data) (c : ℕ) (records : List Partition.Record) :
    (output d c records).tape 10=RepairStage.encTape
      (Partition.encode (Reinsert.fill (RepairScan.flagged (flag d c) 0 records)
        (RepairStage.replacements d.geom.addressBits (RepairScan.items (flag d c) (bits d c) 0 records)))) := rfl

end
end IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineRun
