import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyEarly
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsDecodeBudgetEarly

/-! Literal source and ideal-result arrays for the entire physical format,
repair, decode and cleanup program. Chunks are derived from real record cells. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyLayoutEarly
noncomputable section
open ActiveRepairEarlyKeyOriginalData ActiveRepairEarlyKeyOriginalValid
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankHeadersEndpoint ActiveRepairRankHeadersData
open ActiveRepairLayoutRecordsShape ActiveRepairLayoutRecordsData
open IntegerMultBounds.Compact ActiveRepairLayoutPermutation
open ActiveRepairLayoutRecordsAssemblyEarly
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


def chunks := (inputRecords).map Partition.Record.payload

 theorem records_chunks : ActiveRepairRecordFormatWords.records (chunks d s before after rows offset width hw ha array)=inputRecords :=
  ActiveRepairLayoutRecordsAssemblyCommon.records_payloads_plain E
    (data s (d.n*d.b) (d.n*d.q) before after rows hw ha
      (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha P array))

 theorem chunks_lengths : ∀ xs∈chunks d s before after rows offset width hw ha array,xs.length=s.payload := by
  intro xs hx
  simp only [chunks,records,plain,List.map_map,List.mem_map] at hx
  obtain ⟨i,_,rfl⟩ := hx
  exact data_length _ _ _ _ _ _ _ _ _ _

 theorem chunks_count : (chunks d s before after rows offset width hw ha array).length=rows*2^s.bits := by
  simp only [chunks,List.length_map,records_length,address_width]

 theorem input_raw (headers : Tapes 43 1) :
    (ActiveRepairLayoutRecordsAssemblyEarly.input headers d (chunks d s before after rows offset width hw ha array)).tape 228=
      putWord (fun _ => blank) 0
        ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha P array)).map bitSymbol) := by
  change putWord (fun _ => blank) 0 ((serialize inputRecords).map bitSymbol)=_
  rw [records_serialize]

include h he hw ha hf hr in
theorem output_ideal (headers : Tapes 43 1) :
    (ActiveRepairLayoutRecordsAssemblyEarly.output headers d (chunks d s before after rows offset width hw ha array)).tape 223=
      putWord (fun _ => blank) 0
        ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha TP array)).map bitSymbol) := by
  rw [raw_output,records_chunks,
    ActiveRepairLayoutRecordsPipelineEarly.repaired_serialize d h s before after rows offset width rowBits he hw ha hf hr array]

include h he hw ha hf hr in
theorem runs (headers : Tapes 43 1) (bs ns : List Bool)
    (hbs : Counter.value bs=s.payload) (hns : Counter.value ns=rows*2^s.bits)
    (hb : headers.tape 13=CountedLoopReuseAlphabet.binary bs) (hbh : headers.head 13=1)
    (hn : headers.tape 19=CountedLoopReuseAlphabet.binary ns) (hnh : headers.head 19=1) :
    HoareTime (ActiveRepairLayoutRecordsAssemblyEarly.program d.side)
      (fun v => v=ActiveRepairLayoutRecordsAssemblyEarly.input headers d (chunks d s before after rows offset width hw ha array))
      (fun v => v=ActiveRepairLayoutRecordsAssemblyEarly.output headers d (chunks d s before after rows offset width hw ha array) ∧
        v.tape 223=putWord (fun _ => blank) 0
          ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha TP array)).map bitSymbol))
      (ActiveRepairLayoutRecordsAssemblyEarly.cost d (chunks d s before after rows offset width hw ha array) bs ns s.payload) := by
  have hh := ActiveRepairLayoutRecordsAssemblyEarly.runs headers d h
    (chunks d s before after rows offset width hw ha array) bs ns s.payload
    (chunks_lengths d s before after rows offset width hw ha array) hbs
    (by rw [chunks_count]; exact hns) hb hbh hn hnh
  apply hh.consequence (fun _ h => h) _ le_rfl
  intro v hv
  refine ⟨hv,?_⟩
  rw [hv]
  exact output_ideal d h s before after rows offset width rowBits he hw ha hf hr array headers

include h he hw ha hf hr in
theorem cost_linear (bs ns : List Bool) (hbits : bs.length≤s.payload+1) (D : ℕ) (hrows : 0<rows)
    (hR : d.geom.addressBits+1≤s.payload)
    (hdensity : VaryingControlRepairDensity.earlyDensity d.q d.b d.n*(d.geom.addressBits+1)≤D) :
    ActiveRepairLayoutRecordsAssemblyEarly.cost d (chunks d s before after rows offset width hw ha array) bs ns s.payload≤
      (ActiveRepairEarlyOriginalPipelineBudget.volumeConstant D+86)*(rows*2^s.bits*s.payload)+7*ns.length+58 := by
  have hp : 1≤s.payload := by omega
  have hrepair := ActiveRepairLayoutRecordsDecodeBudgetEarly.repair_cost_linear d h s before after rows offset width rowBits
    he hw ha hf hr array D hrows hR hdensity
  have hflatten := ActiveRepairLayoutRecordsAssemblyCommon.flatten_cost_le
    (ActiveRepairEarlyOriginalPipelineCleanup.repaired d inputRecords) s.payload
    (ActiveRepairLayoutRecordsDecodeEarly.repaired_payloads d h s before after rows offset width rowBits he hw ha hf hr array)
  rw [ActiveRepairLayoutRecordsDecodeEarly.repaired_length d h s before after rows offset width rowBits he hw ha hf hr array] at hflatten
  have hdecode : ActiveRepairLayoutRecordsDecodeEarly.cost d
      (ActiveRepairRecordFormatWords.records (chunks d s before after rows offset width hw ha array))≤
      (ActiveRepairEarlyOriginalPipelineBudget.volumeConstant D+10)*(rows*2^s.bits*s.payload)+13 := by
    rw [records_chunks]
    unfold ActiveRepairLayoutRecordsDecodeEarly.cost
    exact ActiveRepairLayoutRecordsAssemblyCommon.decode_cost_absorb _ _ _ _ _ hp hrepair hflatten
  have hformat := ActiveRepairLayoutRecordsAssemblyCommon.format_cost_le
    (chunks d s before after rows offset width hw ha array) bs ns s.payload
    (chunks_lengths d s before after rows offset width hw ha array) hbits
  have hs := ActiveRepairLayoutRecordsAssemblyCommon.source_length
    (chunks d s before after rows offset width hw ha array) s.payload
    (chunks_lengths d s before after rows offset width hw ha array)
  rw [chunks_count] at hformat hs
  unfold ActiveRepairLayoutRecordsAssemblyEarly.cost
  exact ActiveRepairLayoutRecordsAssemblyCommon.assembly_cost_absorb _ _ _ _ _ _ _ hp hformat hdecode hs

include h he hw ha hf hr in
theorem runs_linear (headers : Tapes 43 1) (bs ns : List Bool)
    (hbs : Counter.value bs=s.payload) (hns : Counter.value ns=rows*2^s.bits)
    (hb : headers.tape 13=CountedLoopReuseAlphabet.binary bs) (hbh : headers.head 13=1)
    (hn : headers.tape 19=CountedLoopReuseAlphabet.binary ns) (hnh : headers.head 19=1)
    (hbits : bs.length≤s.payload+1) (D : ℕ) (hrows : 0<rows)
    (hR : d.geom.addressBits+1≤s.payload)
    (hdensity : VaryingControlRepairDensity.earlyDensity d.q d.b d.n*(d.geom.addressBits+1)≤D) :
    HoareTime (ActiveRepairLayoutRecordsAssemblyEarly.program d.side)
      (fun v => v=ActiveRepairLayoutRecordsAssemblyEarly.input headers d (chunks d s before after rows offset width hw ha array))
      (fun v => v=ActiveRepairLayoutRecordsAssemblyEarly.output headers d (chunks d s before after rows offset width hw ha array) ∧
        v.tape 223=putWord (fun _ => blank) 0
          ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha TP array)).map bitSymbol))
      ((ActiveRepairEarlyOriginalPipelineBudget.volumeConstant D+86)*(rows*2^s.bits*s.payload)+7*ns.length+58) :=
  (runs d h s before after rows offset width rowBits he hw ha hf hr array headers bs ns hbs hns hb hbh hn hnh).consequence
    (fun _ h => h) (fun _ h => h)
    (cost_linear d h s before after rows offset width rowBits he hw ha hf hr array bs ns hbits D hrows hR hdensity)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyLayoutEarly
