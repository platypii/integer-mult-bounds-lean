import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsDecodeLate
import IntegerMultBounds.Machine.ActiveRepairLayoutKeysPipelineBudgetLate

/-! The actual wide-array repair and decoder together have linear physical
payload-volume cost under the manuscript sparse-hole inequalities. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsDecodeBudgetLate
noncomputable section
open ActiveRepairLateKeyOriginalData ActiveRepairLateKeyOriginalValid
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
local notation "P" => lateActual s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "Q" => lateActual (addressShape s) d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "T" => lateIdeal (addressShape s) d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "TP" => lateIdeal s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "B" => lateBad (addressShape s) d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "inputRecords" => records s (d.n*d.b) (d.n*d.q) before after rows hw ha
  (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha P array)
local notation "arrayData" => data s (d.n*d.b) (d.n*d.q) before after rows hw ha array


include h he hw ha hf hr in
theorem repair_cost_linear (D : ℕ) (hrows : 0<rows)
    (hR : d.geom.addressBits+1≤s.payload)
    (hd : VaryingControlRepairDensity.lateDensity d.q d.b d.n*(d.geom.addressBits+1)≤D) :
    ActiveRepairLateOriginalPipelineEndpoint.cost d inputRecords≤
      ActiveRepairLateOriginalPipelineBudget.volumeConstant D*(rows*2^s.bits*s.payload) := by
  have he' : d.geom=geometry (addressShape s) (d.n*d.b) (d.n*d.q) before after offset width rowBits := by
    rw [geometry_address]; exact he
  have hh := ActiveRepairLateOriginalPipelineBudget.cost_linear d (repairRecords E Q arrayData) s.payload D
    (ActiveRepairLayoutKeysPipelineBudgetCommon.records_length_pos E Q arrayData
      (ActiveRepairLayoutKeysPipelineBudgetCommon.volume_pos (addressShape s) rows hrows rfl))
    (ActiveRepairLayoutKeysPipelineBudgetCommon.records_payloads E Q arrayData s.payload
      (fun x => le_of_eq (data_length _ _ _ _ _ _ _ _ _ _))) hR
    (ActiveRepairLayoutKeysPipelineBudgetLate.sparse d h (addressShape s) before after rows offset width rowBits
      he' hw ha rfl hf hr arrayData D hd)
  rw [←ActiveRepairLayoutRecordsPipelineLate.records_actual] at hh
  simpa only [records_length,address_width] using hh

include h he hw ha hf hr in
theorem runs_linear (D : ℕ) (hrows : 0<rows)
    (hR : d.geom.addressBits+1≤s.payload)
    (hd : VaryingControlRepairDensity.lateDensity d.q d.b d.n*(d.geom.addressBits+1)≤D) :
    HoareTime (ActiveRepairLayoutRecordsDecodeLate.program d.side)
      (fun v => v=ActiveRepairLayoutRecordsDecodeLate.input d inputRecords)
      (fun v => v=ActiveRepairLayoutRecordsDecodeLate.output d inputRecords ∧
        v.tape 189=putWord (fun _ => blank) 0
          ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha TP array)).map bitSymbol))
      ((ActiveRepairLateOriginalPipelineBudget.volumeConstant D+10)*(rows*2^s.bits*s.payload)+13) := by
  have hh := ActiveRepairLayoutRecordsDecodeLate.runs_ideal_linear_decode d h s before after rows offset width rowBits
    he hw ha hf hr array
  apply hh.consequence (fun _ h => h) (fun _ h => h)
  have hc := repair_cost_linear d h s before after rows offset width rowBits he hw ha hf hr array D hrows hR hd
  have hp : 1≤s.payload := by omega
  have hd' : 5*(rows*2^s.bits)*(s.payload+1)≤10*(rows*2^s.bits*s.payload) := by
    nlinarith [Nat.mul_le_mul_left (rows*2^s.bits) hp]
  nlinarith

include h he hw ha hf hr in
theorem runs_dyadic (hrows : 0<rows) (hR : d.geom.addressBits+1≤s.payload)
    (p : ℝ) (ell K : ℕ) (hq : d.q=K) (hb : d.b=4*ell+6) (hpos : 0<p)
    (hn : (d.n:ℝ)≤p) (hell : p≤(2:ℝ)^ell) (hK : 8*ell+16≤K)
    (hA : (d.geom.addressBits:ℝ)+1≤p^3) :
    HoareTime (ActiveRepairLayoutRecordsDecodeLate.program d.side)
      (fun v => v=ActiveRepairLayoutRecordsDecodeLate.input d inputRecords)
      (fun v => v=ActiveRepairLayoutRecordsDecodeLate.output d inputRecords ∧
        v.tape 189=putWord (fun _ => blank) 0
          ((List.ofFn (ActiveRepairLayoutRecordsMove.move s (d.n*d.b) (d.n*d.q) before after rows hw ha TP array)).map bitSymbol))
      ((ActiveRepairLateOriginalPipelineBudget.volumeConstant 1+10)*(rows*2^s.bits*s.payload)+13) := by
  apply runs_linear d h s before after rows offset width rowBits he hw ha hf hr array 1 hrows hR
  rw [hq,hb]
  simpa only [Nat.cast_one] using ActiveRepairLayoutDensityArithmetic.dyadic_late_paid p d.n ell K d.geom.addressBits hpos hn hell hK hA

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsDecodeBudgetLate
