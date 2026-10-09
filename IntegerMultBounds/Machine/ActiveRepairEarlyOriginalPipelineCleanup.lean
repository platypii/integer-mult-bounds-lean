import IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelinePrepare
import IntegerMultBounds.Machine.CountedTapeRepairCleanupRun

/-! Erase the actual sorted-key words, all scan sentinels/pass metadata and
counter, and return original source and repaired output to their origins. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineCleanup
noncomputable section
open ActiveRepairEarlyKeyOriginalData
open CountedTapeRepairCleanupRun (recordWord record_tape record_length record_nonblank selector_marked)
open SharedPlacementAlphabet (setTape)

def items (d : Data) (rs : List Partition.Record) :=
  RepairScan.items (ActiveRepairEarlyOriginalScan.flag d d.geom.addressBits)
    (ActiveRepairEarlyOriginalScan.bits d d.geom.addressBits) 0 rs
def flagged (d : Data) (rs : List Partition.Record) :=
  RepairScan.flagged (ActiveRepairEarlyOriginalScan.flag d d.geom.addressBits) 0 rs
def replacements (d : Data) (rs : List Partition.Record) :=
  RepairStage.replacements d.geom.addressBits (items d rs)
def repaired (d : Data) (rs : List Partition.Record) :=
  Reinsert.fill (flagged d rs) (replacements d rs)
def index (d : Data) (rs : List Partition.Record) :=
  TapeRadixSort.completed d.geom.addressBits (RepairStage.raw (items d rs))
def sortedWord (d : Data) (rs : List Partition.Record) :=
  KeySelect.encode (RepairStage.sortedRaw d.geom.addressBits (items d rs))
def counter (d : Data) (rs : List Partition.Record) := RepairScan.counter d.geom.addressBits rs.length

def input (d : Data) (rs : List Partition.Record) :=
  (ActiveRepairEarlyOriginalPipelineRun.output d d.geom.addressBits rs).append (SharedBank.empty 3 1)
def output (d : Data) (rs : List Partition.Record) := setTape
  (ActiveRepairEarlyOriginalPipelinePrepare.input d rs) 10
  (RepairStage.encTape (Partition.encode (repaired d rs))) 0

def leftBank (v : Tapes 183 1) : Tapes 42 1 := SharedBank.payload v (Fin.castAdd 141)
def rightBank (v : Tapes 183 1) : Tapes 141 1 := SharedBank.payload v (Fin.natAdd 42)
def program := extend CountedTapeRepairCleanup.program 141

theorem split (v : Tapes 183 1) : (leftBank v).append (rightBank v)=v := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i => simp only [Fin.addCases_left]; rfl
  | right i => simp only [Fin.addCases_right]; rfl

def cost (d : Data) (rs : List Partition.Record) :=
  (sortedWord d rs).length+2*index d rs+4*d.geom.addressBits+
    (Partition.encode (replacements d rs)).length+(Partition.encode (flagged d rs)).length+
    (Partition.encode (repaired d rs)).length+(DropFlag.encode rs).length+72

theorem output_eq (d : Data) (rs : List Partition.Record) :
    (CountedTapeRepairCleanup.output (leftBank (input d rs))
      (recordWord (repaired d rs)) (recordWord rs)).append (rightBank (input d rs))=output d rs := by
  have he0 := record_tape (repaired d rs)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact he0

theorem runs (d : Data) (rs : List Partition.Record) :
    HoareTime program (fun v => v=input d rs) (fun v => v=output d rs) (cost d rs) := by
  let v := leftBank (input d rs)
  have h8 : v.tape 8=putWord (fun _ => blank) 0 (recordWord (replacements d rs)) := (record_tape _).symm
  have h9 : v.tape 9=putWord (fun _ => blank) 0 (recordWord (flagged d rs)) := (record_tape _).symm
  have h10 : v.tape 10=putWord (fun _ => blank) 0 (recordWord (repaired d rs)) := (record_tape _).symm
  have hp8 : v.head 8=(recordWord (replacements d rs)).length := by rw [record_length]; rfl
  have hp9 : v.head 9=(recordWord (flagged d rs)).length := by rw [record_length]; rfl
  have hp10 : v.head 10=(recordWord (repaired d rs)).length := by rw [record_length]; rfl
  have hh := CountedTapeRepairCleanup.runs v (sortedWord d rs)
    (List.replicate (index d rs) (bitSymbol true)) (List.replicate d.geom.addressBits (bitSymbol true))
    (recordWord (replacements d rs)) (recordWord (flagged d rs)) (recordWord (repaired d rs))
    (recordWord rs) (counter d rs)
    rfl rfl (selector_marked _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (selector_marked _) rfl
    h8 hp8 h9 hp9 h10 hp10 rfl rfl rfl rfl rfl rfl
    (RepairStage.encode_nonblank _)
    (by intro x hx; simp only [List.mem_replicate] at hx; rcases hx with ⟨_,rfl⟩; decide)
    (by intro x hx; simp only [List.mem_replicate] at hx; rcases hx with ⟨_,rfl⟩; decide)
    (record_nonblank _) (record_nonblank _) (record_nonblank _) (record_nonblank _)
  have h := hoare_extend_eq hh (rightBank (input d rs))
  change HoareTime program (fun w => w=(leftBank (input d rs)).append (rightBank (input d rs)))
    (fun w => w=(CountedTapeRepairCleanup.output (leftBank (input d rs))
      (recordWord (repaired d rs)) (recordWord rs)).append (rightBank (input d rs))) _ at h
  rw [split,output_eq] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by
    simp only [List.length_replicate,record_length,counter,RepairScan.counter_length]
    unfold cost
    have hr := record_length rs
    change (DropFlag.encode rs).length=(Partition.encode rs).length at hr
    rw [←hr]
    omega)

end
end IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineCleanup
