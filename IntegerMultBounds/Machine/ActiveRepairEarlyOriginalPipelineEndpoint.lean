import IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineCleanup

/-! Actual original-input early repair from literal source and blank scan
workspace through preparation, varying-rank scan, sort/reinsert and complete
final cleanup. Only original source, metadata and repaired output survive. -/
namespace IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineEndpoint
noncomputable section
open ActiveRepairEarlyKeyOriginalData ActiveRepairEarlyKeyOriginalValid
open SharedPlacementAlphabet (setTape)

def bodyProgram (side : ActiveRepairRankHeadersData.SourceSide) :=
  extend (ActiveRepairEarlyOriginalPipelineRun.program side) 3
def program (side : ActiveRepairRankHeadersData.SourceSide) := seq
  (seq ActiveRepairEarlyOriginalPipelinePrepare.program (bodyProgram side))
  ActiveRepairEarlyOriginalPipelineCleanup.program
def input := ActiveRepairEarlyOriginalPipelinePrepare.input
def output := ActiveRepairEarlyOriginalPipelineCleanup.output
def cost (d : Data) (rs : List Partition.Record) :=
  200*(d.geom.addressBits+1)+1+
    ActiveRepairEarlyOriginalPipelineRun.cost d d.geom.addressBits rs+1+
    ActiveRepairEarlyOriginalPipelineCleanup.cost d rs

theorem runs (d : Data) (h : Valid d) (rs : List Partition.Record) :
    HoareTime (program d.side) (fun v => v=input d rs) (fun v => v=output d rs) (cost d rs) := by
  have hp := ActiveRepairEarlyOriginalPipelinePrepare.runs_linear d h rs
  have hb := hoare_extend_eq (ActiveRepairEarlyOriginalPipelineRun.runs d h d.geom.addressBits rs)
    (SharedBank.empty 3 1)
  exact (hp.seq hb).seq (ActiveRepairEarlyOriginalPipelineCleanup.runs d rs)

theorem output_tape (d : Data) (rs : List Partition.Record) :
    (output d rs).tape 10=RepairStage.encTape
      (Partition.encode (ActiveRepairEarlyOriginalPipelineCleanup.repaired d rs)) := rfl

theorem source_tape (d : Data) (rs : List Partition.Record) :
    (output d rs).tape 11=RepairScan.srcTape rs := rfl

def scanSlot (i : Fin 14) : Fin 183 := Fin.castAdd 3 (Fin.castAdd 166 i)
def metadataSlot (i : Fin 166) : Fin 183 := Fin.castAdd 3 (Fin.natAdd 14 i)

theorem heads_at_origin (d : Data) (rs : List Partition.Record) (i : Fin 14) :
    (output d rs).head (scanSlot i)=0 := by
  fin_cases i <;> rfl

theorem scan_blank (d : Data) (rs : List Partition.Record) (i : Fin 14) (hi : i≠10) (hs : i≠11) :
    (output d rs).tape (scanSlot i)=fun _ => blank := by
  fin_cases i <;> first | rfl | exact (hi rfl).elim | exact (hs rfl).elim

theorem metadata_retained (d : Data) (rs : List Partition.Record) :
    SharedBank.payload (output d rs) metadataSlot=ActiveRepairEarlyOriginalScan.scratch d := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem auxiliary_blank (d : Data) (rs : List Partition.Record) :
    SharedBank.payload (output d rs) (Fin.natAdd 180)=SharedBank.empty 3 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineEndpoint
