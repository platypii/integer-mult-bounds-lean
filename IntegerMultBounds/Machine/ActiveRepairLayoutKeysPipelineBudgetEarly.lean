import IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineBudgetCommon
import IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineEarly
import IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineBudget

/-! Linear runtime for the concrete ideal-output repair endpoint. The sparse
holes are counted from the physical flags and the complete global layout. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineBudgetEarly
noncomputable section
attribute [local instance] Classical.propDecidable
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankHeadersEndpoint ActiveRepairRankHeadersData
open ActiveRepairEarlyKeyOriginalData ActiveRepairEarlyKeyOriginalValid
open IntegerMultBounds.Compact
open ActiveRepairLayoutKeysPipelineBudgetCommon
variable (d : Data) (h : Valid d) (s : Shape) (before after rows offset width rowBits : ℕ)
variable (he : d.geom=geometry s (d.n*d.b) (d.n*d.q) before after offset width rowBits)
variable (hw : d.n*d.b≤s.H) (ha : before+d.n*d.q+after=s.active*s.chunk) (hp : s.payload=1)
variable (hf : sourceFits d.side before after offset width) (hr : rows≤2^rowBits)
local notation "E" => indexEquiv s (d.n*d.b) (d.n*d.q) before after rows hw ha
local notation "S" => ActiveRepairLayoutPermutation.earlyActual s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysEarly.positive d)
local notation "T" => ActiveRepairLayoutPermutation.earlyIdeal s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysEarly.positive d)
local notation "B" => ActiveRepairLayoutPermutation.earlyBad s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysEarly.positive d)
variable (data : Address s (d.n*d.b) (d.n*d.q) before after rows → List Bool)


include h he hw ha hp hf hr in
theorem sparse (D : ℕ)
    (hd : VaryingControlRepairDensity.earlyDensity d.q d.b d.n*(d.geom.addressBits+1)≤D) :
    ActiveRepairEarlyOriginalPipelineBudget.holes d (repairRecords E S data)*(d.geom.addressBits+1)≤
      D*(repairRecords E S data).length := by
  have hA : d.geom.addressBits=s.bits+rowBits := by simp only [he,geometry]
  have hc : rows*s.recordWidth≤2^d.geom.addressBits := by
    rw [hA]
    exact ActiveRepairLayoutKeysPipelineCommon.counter_bound s rows rowBits hp hr
  have hflag := ActiveRepairLayoutKeysScanEarly.flag d h s before after rows offset width rowBits he hw ha hp hf d.geom.addressBits hc
  exact ActiveRepairLayoutDensityScan.sparse_plain E B (data ∘ (S).symm) _ hflag _ _ D
    (ActiveRepairLayoutDensity.early_bad_count s d.q d.b d.n before after rows d.rho offset width d.side
      (ActiveRepairLayoutKeysEarly.positive d) h.hbq3) hd

include h he hw ha hp hf hr in
theorem runs_linear (R D : ℕ) (hrows : 0<rows) (hdata : ∀ x,(data x).length≤R)
    (hR : d.geom.addressBits+1≤R)
    (hd : VaryingControlRepairDensity.earlyDensity d.q d.b d.n*(d.geom.addressBits+1)≤D) :
    HoareTime (ActiveRepairEarlyOriginalPipelineEndpoint.program d.side)
      (fun v => v=ActiveRepairEarlyOriginalPipelineEndpoint.input d (repairRecords E S data))
      (fun v => v=ActiveRepairEarlyOriginalPipelineEndpoint.output d (repairRecords E S data) ∧
        v.tape 10=RepairStage.encTape (Partition.encode (stream E B (data ∘ (T).symm))))
      (ActiveRepairEarlyOriginalPipelineBudget.volumeConstant D*((repairRecords E S data).length*R)) := by
  have hh := ActiveRepairLayoutKeysPipelineEarly.runs d h s before after rows offset width rowBits he hw ha hp hf hr data
  exact hh.consequence (fun _ hv => hv) (fun _ hv => hv)
    (ActiveRepairEarlyOriginalPipelineBudget.cost_linear d (repairRecords E S data) R D
      (records_length_pos E S data (volume_pos s rows hrows hp))
      (records_payloads E S data R hdata) hR
      (sparse d h s before after rows offset width rowBits he hw ha hp hf hr data D hd))

include h he hw ha hp hf hr in
theorem runs_dyadic (R : ℕ) (hrows : 0<rows) (hdata : ∀ x,(data x).length≤R)
    (hR : d.geom.addressBits+1≤R) (p : ℝ) (ell K : ℕ)
    (hq : d.q=K) (hb : d.b=4*ell+6) (hpos : 0<p) (hn : (d.n:ℝ)≤p)
    (hell : p≤(2:ℝ)^ell) (hK : 8*ell+16≤K) (hA : (d.geom.addressBits:ℝ)+1≤p^3) :
    HoareTime (ActiveRepairEarlyOriginalPipelineEndpoint.program d.side)
      (fun v => v=ActiveRepairEarlyOriginalPipelineEndpoint.input d (repairRecords E S data))
      (fun v => v=ActiveRepairEarlyOriginalPipelineEndpoint.output d (repairRecords E S data) ∧
        v.tape 10=RepairStage.encTape (Partition.encode (stream E B (data ∘ (T).symm))))
      (ActiveRepairEarlyOriginalPipelineBudget.volumeConstant 1*((repairRecords E S data).length*R)) := by
  apply runs_linear d h s before after rows offset width rowBits he hw ha hp hf hr data R 1 hrows hdata hR
  rw [hq,hb]
  simpa only [Nat.cast_one] using ActiveRepairLayoutDensityArithmetic.dyadic_early_paid p d.n ell K d.geom.addressBits hpos hn hell hK hA

end
end IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineBudgetEarly
