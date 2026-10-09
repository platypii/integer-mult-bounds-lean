import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsMove
import IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineLate

/-! Full-width physical records use payload-one repair addresses and original
geometry unchanged. The checked repair endpoint yields exact ideal records and
semantic serialization to the full physical ideal array. Formatting is separate. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPipelineLate
noncomputable section
attribute [local instance] Classical.propDecidable
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankHeadersEndpoint ActiveRepairRankHeadersData
open ActiveRepairLateKeyOriginalData ActiveRepairLateKeyOriginalValid
open ActiveRepairLayoutRecordsShape ActiveRepairLayoutRecordsData
open IntegerMultBounds.Compact ActiveRepairLayoutPermutation
variable (d : Data) (h : Valid d) (s : Shape) (before after rows offset width rowBits : ℕ)
variable (he : d.geom=geometry s (d.n*d.b) (d.n*d.q) before after offset width rowBits)
variable (hw : d.n*d.b≤s.H) (ha : before+d.n*d.q+after=s.active*s.chunk)
variable (hf : sourceFits d.side before after offset width) (hr : rows≤2^rowBits)
variable (array : Array s rows)
local notation "E" => indexEquiv (addressShape s) (d.n*d.b) (d.n*d.q) before after rows hw ha
local notation "P" => lateActual s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "Q" => lateActual (addressShape s) d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "T" => lateIdeal (addressShape s) d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "TP" => lateIdeal s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "B" => lateBad (addressShape s) d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "inputRecords" => records s (d.n*d.b) (d.n*d.q) before after rows hw ha
  (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha P array)
local notation "arrayData" => data s (d.n*d.b) (d.n*d.q) before after rows hw ha array

theorem records_actual : inputRecords=repairRecords E Q arrayData := by
  unfold records repairRecords
  rw [ActiveRepairLayoutRecordsMove.data_move s (d.n*d.b) (d.n*d.q) before after rows hw ha P Q array
    (ActiveRepairLayoutRecordsPermutation.late_actual s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d))]

include h he hw ha hf hr in
theorem repaired : ActiveRepairLateOriginalPipelineCleanup.repaired d inputRecords=
    stream E B (arrayData ∘ (T).symm) := by
  rw [records_actual]
  have he' : d.geom=geometry (addressShape s) (d.n*d.b) (d.n*d.q) before after offset width rowBits := by
    rw [geometry_address]; exact he
  exact ActiveRepairLayoutKeysPipelineLate.repaired d h (addressShape s) before after rows offset width rowBits
    he' hw ha rfl hf hr arrayData

include h he hw ha hf hr in
theorem repaired_serialize : serialize (ActiveRepairLateOriginalPipelineCleanup.repaired d inputRecords)=
    List.ofFn (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha TP array) := by
  rw [repaired d h s before after rows offset width rowBits he hw ha hf hr array]
  exact ActiveRepairLayoutRecordsMove.serialize_move s (d.n*d.b) (d.n*d.q) before after rows hw ha TP T array B
    (ActiveRepairLayoutRecordsPermutation.late_ideal s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d))

include h he hw ha hf hr in
theorem runs :
    HoareTime (ActiveRepairLateOriginalPipelineEndpoint.program d.side)
      (fun v => v=ActiveRepairLateOriginalPipelineEndpoint.input d inputRecords)
      (fun v => v=ActiveRepairLateOriginalPipelineEndpoint.output d inputRecords ∧
        v.tape 10=RepairStage.encTape (Partition.encode (stream E B (arrayData ∘ (T).symm))))
      (ActiveRepairLateOriginalPipelineEndpoint.cost d inputRecords) := by
  have hh := ActiveRepairLateOriginalPipelineEndpoint.runs d h inputRecords
  apply hh.consequence (fun _ hv => hv) _ (le_refl _)
  intro v hv
  refine ⟨hv,?_⟩
  rw [hv,ActiveRepairLateOriginalPipelineEndpoint.output_tape,
    repaired d h s before after rows offset width rowBits he hw ha hf hr array]

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPipelineLate
