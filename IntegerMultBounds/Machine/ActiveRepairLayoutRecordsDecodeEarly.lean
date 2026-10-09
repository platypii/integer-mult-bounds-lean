import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsDecodeCommon
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPipelineEarly

/-! Actual repair followed by the literal raw decoder. Decoding destroys the
repaired record buffer, emits ideal payload bits in a clean auxiliary port,
and restores its appended private bank without changing caller metadata. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsDecodeEarly
noncomputable section
open SharedPlacementAlphabet (setTape)
open ActiveRepairEarlyKeyOriginalData ActiveRepairEarlyKeyOriginalValid

def focus : Fin 2 → Fin 183 := ![10,180]
theorem focus_injective : Function.Injective focus := by
  intro i j hh
  fin_cases i <;> fin_cases j <;> simp [focus] at hh ⊢
def input (d : Data) (rs : List Partition.Record) :=
  CleanSubbank.bank (s:=2) (ActiveRepairEarlyOriginalPipelineEndpoint.input d rs)
def output (d : Data) (rs : List Partition.Record) := CleanSubbank.bank (s:=2)
  (ActiveRepairRecordFlattenPlaced.result (a:=0) (ActiveRepairEarlyOriginalPipelineEndpoint.output d rs) focus
    (ActiveRepairEarlyOriginalPipelineCleanup.repaired d rs))
def program (side : ActiveRepairRankHeadersData.SourceSide) := seq
  (extend (ActiveRepairEarlyOriginalPipelineEndpoint.program side) 2)
  (ActiveRepairRecordFlattenPlaced.program (a:=0) focus focus_injective)
def cost (d : Data) (rs : List Partition.Record) :=
  ActiveRepairEarlyOriginalPipelineEndpoint.cost d rs+1+
    ActiveRepairRecordFlattenOriginal.cost (ActiveRepairEarlyOriginalPipelineCleanup.repaired d rs)

 theorem decoder_ready (d : Data) (rs : List Partition.Record) :
    SharedBank.payload (ActiveRepairEarlyOriginalPipelineEndpoint.output d rs) focus=
      ActiveRepairRecordFlattenAlphabet.input 0 (ActiveRepairEarlyOriginalPipelineCleanup.repaired d rs) := by
  rw [ActiveRepairLayoutRecordsDecodeCommon.decoder_input]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

 theorem runs (d : Data) (h : Valid d) (rs : List Partition.Record) :
    HoareTime (program d.side) (fun v => v=input d rs) (fun v => v=output d rs) (cost d rs) := by
  have hb := hoare_extend_eq (ActiveRepairEarlyOriginalPipelineEndpoint.runs d h rs) (SharedBank.empty 2 1)
  have hd := ActiveRepairRecordFlattenPlaced.runs (a:=0) (ActiveRepairEarlyOriginalPipelineEndpoint.output d rs)
    focus focus_injective (ActiveRepairEarlyOriginalPipelineCleanup.repaired d rs) (decoder_ready d rs)
  exact hb.seq hd

 theorem runs_linear_decode (d : Data) (h : Valid d) (rs : List Partition.Record) (R : ℕ)
    (hw : ∀ r∈ActiveRepairEarlyOriginalPipelineCleanup.repaired d rs,r.payload.length≤R) :
    HoareTime (program d.side) (fun v => v=input d rs) (fun v => v=output d rs)
      (ActiveRepairEarlyOriginalPipelineEndpoint.cost d rs+
        5*(ActiveRepairEarlyOriginalPipelineCleanup.repaired d rs).length*(R+1)+13) := by
  have hb := hoare_extend_eq (ActiveRepairEarlyOriginalPipelineEndpoint.runs d h rs) (SharedBank.empty 2 1)
  have hd := ActiveRepairRecordFlattenPlaced.runs_linear (a:=0) (ActiveRepairEarlyOriginalPipelineEndpoint.output d rs)
    focus focus_injective (ActiveRepairEarlyOriginalPipelineCleanup.repaired d rs) R hw (decoder_ready d rs)
  exact (hb.seq hd).consequence (fun _ h => h) (fun _ h => h) (by omega)

 theorem record_buffer_blank (d : Data) (rs : List Partition.Record) :
    (output d rs).tape 10=fun _ => blank := rfl
 theorem source_retained (d : Data) (rs : List Partition.Record) :
    (output d rs).tape 11=RepairScan.srcTape rs := rfl
 theorem private_blank (d : Data) (rs : List Partition.Record) :
    SharedBank.payload (output d rs) (Fin.natAdd 183)=SharedBank.empty 2 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
 theorem raw_output (d : Data) (rs : List Partition.Record) :
    (output d rs).tape 180=putWord (fun _ => blank) 0
      ((ActiveRepairLayoutRecordsData.serialize (ActiveRepairEarlyOriginalPipelineCleanup.repaired d rs)).map bitSymbol) := rfl
 theorem raw_head_origin (d : Data) (rs : List Partition.Record) : (output d rs).head 180=0 := rfl

open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankHeadersEndpoint ActiveRepairRankHeadersData
open ActiveRepairLayoutRecordsShape ActiveRepairLayoutRecordsData
open IntegerMultBounds.Compact ActiveRepairLayoutPermutation
variable (d : Data) (h : Valid d) (s : Shape) (before after rows offset width rowBits : ℕ)
variable (he : d.geom=geometry s (d.n*d.b) (d.n*d.q) before after offset width rowBits)
variable (hw : d.n*d.b≤s.H) (ha : before+d.n*d.q+after=s.active*s.chunk)
variable (hf : sourceFits d.side before after offset width) (hr : rows≤2^rowBits)
variable (array : Array s rows)
local notation "E" => indexEquiv (addressShape s) (d.n*d.b) (d.n*d.q) before after rows hw ha
local notation "P" => earlyActual s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysEarly.positive d)
local notation "Q" => earlyActual (addressShape s) d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysEarly.positive d)
local notation "T" => earlyIdeal (addressShape s) d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysEarly.positive d)
local notation "TP" => earlyIdeal s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysEarly.positive d)
local notation "B" => earlyBad (addressShape s) d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysEarly.positive d)
local notation "inputRecords" => records s (d.n*d.b) (d.n*d.q) before after rows hw ha
  (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha P array)
local notation "arrayData" => data s (d.n*d.b) (d.n*d.q) before after rows hw ha array


include h he hw ha hf hr in
theorem ideal_raw_output : (output d inputRecords).tape 180=putWord (fun _ => blank) 0
    ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha TP array)).map bitSymbol) := by
  rw [raw_output,ActiveRepairLayoutRecordsPipelineEarly.repaired_serialize d h s before after rows offset width rowBits he hw ha hf hr array]

include h he hw ha hf hr in
theorem runs_ideal : HoareTime (program d.side) (fun v => v=input d inputRecords)
    (fun v => v=output d inputRecords ∧ v.tape 180=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha TP array)).map bitSymbol))
    (cost d inputRecords) := by
  apply (runs d h inputRecords).consequence (fun _ h => h) _ le_rfl
  intro v hv
  refine ⟨hv,?_⟩
  rw [hv]
  exact ideal_raw_output d h s before after rows offset width rowBits he hw ha hf hr array

include h he hw ha hf hr in
theorem repaired_length :
    (ActiveRepairEarlyOriginalPipelineCleanup.repaired d inputRecords).length=rows*2^s.bits := by
  rw [ActiveRepairLayoutRecordsPipelineEarly.repaired d h s before after rows offset width rowBits he hw ha hf hr array]
  simp only [stream,List.length_map,List.length_finRange,address_width]

include h he hw ha hf hr in
theorem repaired_payloads :
    ∀ r ∈ ActiveRepairEarlyOriginalPipelineCleanup.repaired d inputRecords,r.payload.length≤s.payload := by
  rw [ActiveRepairLayoutRecordsPipelineEarly.repaired d h s before after rows offset width rowBits he hw ha hf hr array]
  intro r hh
  simp only [stream,List.mem_map] at hh
  obtain ⟨i,_,rfl⟩ := hh
  exact le_of_eq (data_length _ _ _ _ _ _ _ _ _ _)

include h he hw ha hf hr in
theorem runs_ideal_linear_decode : HoareTime (program d.side) (fun v => v=input d inputRecords)
    (fun v => v=output d inputRecords ∧ v.tape 180=putWord (fun _ => blank) 0
      ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha TP array)).map bitSymbol))
    (ActiveRepairEarlyOriginalPipelineEndpoint.cost d inputRecords+5*(rows*2^s.bits)*(s.payload+1)+13) := by
  have hh := runs_linear_decode d h inputRecords s.payload
    (repaired_payloads d h s before after rows offset width rowBits he hw ha hf hr array)
  rw [repaired_length d h s before after rows offset width rowBits he hw ha hf hr array] at hh
  apply hh.consequence (fun _ h => h) _ le_rfl
  intro v hv
  refine ⟨hv,?_⟩
  rw [hv]
  exact ideal_raw_output d h s before after rows offset width rowBits he hw ha hf hr array

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsDecodeEarly
