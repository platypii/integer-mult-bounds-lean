import IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineCommon
import IntegerMultBounds.Machine.ActiveRepairLateOriginalPipelineEndpoint

/-! The actual original-input repair endpoint produces the concrete global
ideal permutation, while retaining its complete exact bank and runtime. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineLate
noncomputable section
attribute [local instance] Classical.propDecidable
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankHeadersEndpoint ActiveRepairRankHeadersData
open ActiveRepairLateKeyOriginalData ActiveRepairLateKeyOriginalValid
open IntegerMultBounds.Compact

variable (d : Data) (h : Valid d) (s : Shape) (before after rows offset width rowBits : ℕ)
variable (he : d.geom=geometry s (d.n*d.b) (d.n*d.q) before after offset width rowBits)
variable (hw : d.n*d.b≤s.H) (ha : before+d.n*d.q+after=s.active*s.chunk) (hp : s.payload=1)
variable (hf : sourceFits d.side before after offset width) (hr : rows≤2^rowBits)
local notation "E" => indexEquiv s (d.n*d.b) (d.n*d.q) before after rows hw ha
local notation "S" => ActiveRepairLayoutPermutation.lateActual s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "T" => ActiveRepairLayoutPermutation.lateIdeal s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "B" => ActiveRepairLayoutPermutation.lateBad s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
variable (data : Address s (d.n*d.b) (d.n*d.q) before after rows → List Bool)

include h he hw ha hp hf hr in
theorem repaired :
    ActiveRepairLateOriginalPipelineCleanup.repaired d (repairRecords E S data)=
      stream E B (data ∘ (T).symm) := by
  have hA : d.geom.addressBits=s.bits+rowBits := by simp only [he,geometry]
  have hc : rows*s.recordWidth≤2^d.geom.addressBits := by
    rw [hA]
    exact ActiveRepairLayoutKeysPipelineCommon.counter_bound s rows rowBits hp hr
  have hflag := ActiveRepairLayoutKeysScanLate.flag d h s before after rows offset width rowBits he hw ha hp hf d.geom.addressBits hc
  have hbits := ActiveRepairLayoutKeysScanLate.destination d h s before after rows offset width rowBits he hw ha hp hf d.geom.addressBits hc hr
  unfold ActiveRepairLateOriginalPipelineCleanup.repaired
    ActiveRepairLateOriginalPipelineCleanup.flagged ActiveRepairLateOriginalPipelineCleanup.replacements
    ActiveRepairLateOriginalPipelineCleanup.items repairRecords
  rw [ActiveRepairLayoutKeysPipelineCommon.flagged_plain E B (data ∘ (S).symm) _ hflag,
    ActiveRepairLayoutKeysPipelineCommon.items_plain E S T B (s.bits+rowBits) data _ _ hflag hbits,hA,
    replacements_eq]
  exact pipeline_exact E S T B
    (ActiveRepairLayoutPermutation.late_preserves s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d))
    (ActiveRepairLayoutPermutation.late_agrees s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d))
    (s.bits+rowBits) (ActiveRepairLayoutKeysPipelineCommon.counter_bound s rows rowBits hp hr) data

include h he hw ha hp hf hr in
theorem output_tape :
    (ActiveRepairLateOriginalPipelineEndpoint.output d (repairRecords E S data)).tape 10=
      RepairStage.encTape (Partition.encode (stream E B (data ∘ (T).symm))) := by
  rw [ActiveRepairLateOriginalPipelineEndpoint.output_tape,
    repaired d h s before after rows offset width rowBits he hw ha hp hf hr data]

include h he hw ha hp hf hr in
theorem runs :
    HoareTime (ActiveRepairLateOriginalPipelineEndpoint.program d.side)
      (fun v => v=ActiveRepairLateOriginalPipelineEndpoint.input d (repairRecords E S data))
      (fun v => v=ActiveRepairLateOriginalPipelineEndpoint.output d (repairRecords E S data) ∧
        v.tape 10=RepairStage.encTape (Partition.encode (stream E B (data ∘ (T).symm))))
      (ActiveRepairLateOriginalPipelineEndpoint.cost d (repairRecords E S data)) := by
  have hh := ActiveRepairLateOriginalPipelineEndpoint.runs d h (repairRecords E S data)
  apply hh.consequence (fun _ hv => hv) _ (le_refl _)
  intro v hv
  refine ⟨hv,?_⟩
  rw [hv]
  exact output_tape d h s before after rows offset width rowBits he hw ha hp hf hr data

end
end IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineLate
