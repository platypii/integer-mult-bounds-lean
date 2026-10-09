import IntegerMultBounds.Machine.ActiveRepairLayoutKeysEarly
import IntegerMultBounds.Machine.ActiveRepairLayoutKeysLate
import IntegerMultBounds.Machine.ActiveRepairEarlyOriginalScan
import IntegerMultBounds.Machine.ActiveRepairLateOriginalScan

/-! Every genuine growing scan rank generates the concrete global membership
flag and ideal-after-actual-inverse full destination, for both source cases. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutKeysScanEarly
noncomputable section
attribute [local instance] Classical.propDecidable
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankHeadersEndpoint ActiveRepairRankHeadersData
open ActiveRepairEarlyKeyOriginalData ActiveRepairEarlyKeyOriginalValid
open IntegerMultBounds.Compact

variable (d : Data) (h : Valid d) (s : Shape) (before after rows offset width rowBits : ℕ)
variable (he : d.geom=geometry s (d.n*d.b) (d.n*d.q) before after offset width rowBits)
variable (hw : d.n*d.b≤s.H) (ha : before+d.n*d.q+after=s.active*s.chunk) (hp : s.payload=1)
variable (hf : sourceFits d.side before after offset width) (c : ℕ) (hcounter : rows*s.recordWidth≤2^c)
local notation "E" => indexEquiv s (d.n*d.b) (d.n*d.q) before after rows hw ha
local notation "S" => ActiveRepairLayoutPermutation.earlyActual s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysEarly.positive d)
local notation "T" => ActiveRepairLayoutPermutation.earlyIdeal s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysEarly.positive d)
local notation "B" => ActiveRepairLayoutPermutation.earlyBad s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysEarly.positive d)

include h he hw ha hp hf hcounter in
theorem flag (j : ℕ) (hj : j<rows*s.recordWidth) :
    ActiveRepairEarlyOriginalScan.flag d c j=rankFlag E B j := by
  let x := (E).symm ⟨j,hj⟩
  have hc : Counter.value (RepairScan.counter c j)=(index s (d.n*d.b) (d.n*d.q) before after rows hw ha x).val := by
    change Counter.value (BinaryAddressTableData.row c j)=_
    rw [BinaryAddressTableData.row_rank c j (lt_of_lt_of_le hj hcounter)]
    exact (congrArg Fin.val ((E).apply_symm_apply ⟨j,hj⟩)).symm
  have hh := ActiveRepairLayoutKeysEarly.flag (ActiveRepairEarlyOriginalScan.withCounter d (RepairScan.counter c j))
    (ActiveRepairEarlyOriginalScan.valid_counter d h _) s before after rows offset width rowBits he hw ha hp hf x hc
  change ActiveRepairEarlyOriginalScan.flag d c j = rankFlag E B (E x).val at hh
  have hx : (E x).val=j := congrArg Fin.val ((E).apply_symm_apply ⟨j,hj⟩)
  rw [hx] at hh
  exact hh

include h he hw ha hp hf hcounter in
theorem destination (hr : rows≤2^rowBits) (j : ℕ) (hj : j<rows*s.recordWidth) :
    ActiveRepairEarlyOriginalScan.bits d c j=rankKey E S T (s.bits+rowBits) j := by
  let x := (E).symm ⟨j,hj⟩
  have hc : Counter.value (RepairScan.counter c j)=(index s (d.n*d.b) (d.n*d.q) before after rows hw ha x).val := by
    change Counter.value (BinaryAddressTableData.row c j)=_
    rw [BinaryAddressTableData.row_rank c j (lt_of_lt_of_le hj hcounter)]
    exact (congrArg Fin.val ((E).apply_symm_apply ⟨j,hj⟩)).symm
  have hh := ActiveRepairLayoutKeysEarly.destination (ActiveRepairEarlyOriginalScan.withCounter d (RepairScan.counter c j))
    (ActiveRepairEarlyOriginalScan.valid_counter d h _) s before after rows offset width rowBits he hw ha hp hf x hc hr
  change ActiveRepairEarlyOriginalScan.bits d c j = rankKey E S T (s.bits+rowBits) (E x).val at hh
  have hx : (E x).val=j := congrArg Fin.val ((E).apply_symm_apply ⟨j,hj⟩)
  rw [hx] at hh
  exact hh

end
end IntegerMultBounds.Machine.ActiveRepairLayoutKeysScanEarly

namespace IntegerMultBounds.Machine.ActiveRepairLayoutKeysScanLate
noncomputable section
attribute [local instance] Classical.propDecidable
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankHeadersEndpoint ActiveRepairRankHeadersData
open ActiveRepairLateKeyOriginalData ActiveRepairLateKeyOriginalValid
open IntegerMultBounds.Compact

variable (d : Data) (h : Valid d) (s : Shape) (before after rows offset width rowBits : ℕ)
variable (he : d.geom=geometry s (d.n*d.b) (d.n*d.q) before after offset width rowBits)
variable (hw : d.n*d.b≤s.H) (ha : before+d.n*d.q+after=s.active*s.chunk) (hp : s.payload=1)
variable (hf : sourceFits d.side before after offset width) (c : ℕ) (hcounter : rows*s.recordWidth≤2^c)
local notation "E" => indexEquiv s (d.n*d.b) (d.n*d.q) before after rows hw ha
local notation "S" => ActiveRepairLayoutPermutation.lateActual s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "T" => ActiveRepairLayoutPermutation.lateIdeal s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)
local notation "B" => ActiveRepairLayoutPermutation.lateBad s d.q d.b d.n before after rows d.rho offset width d.side (ActiveRepairLayoutKeysLate.positive d)

include h he hw ha hp hf hcounter in
theorem flag (j : ℕ) (hj : j<rows*s.recordWidth) :
    ActiveRepairLateOriginalScan.flag d c j=rankFlag E B j := by
  let x := (E).symm ⟨j,hj⟩
  have hc : Counter.value (RepairScan.counter c j)=(index s (d.n*d.b) (d.n*d.q) before after rows hw ha x).val := by
    change Counter.value (BinaryAddressTableData.row c j)=_
    rw [BinaryAddressTableData.row_rank c j (lt_of_lt_of_le hj hcounter)]
    exact (congrArg Fin.val ((E).apply_symm_apply ⟨j,hj⟩)).symm
  have hh := ActiveRepairLayoutKeysLate.flag (ActiveRepairLateOriginalScan.withCounter d (RepairScan.counter c j))
    (ActiveRepairLateOriginalScan.valid_counter d h _) s before after rows offset width rowBits he hw ha hp hf x hc
  change ActiveRepairLateOriginalScan.flag d c j = rankFlag E B (E x).val at hh
  have hx : (E x).val=j := congrArg Fin.val ((E).apply_symm_apply ⟨j,hj⟩)
  rw [hx] at hh
  exact hh

include h he hw ha hp hf hcounter in
theorem destination (hr : rows≤2^rowBits) (j : ℕ) (hj : j<rows*s.recordWidth) :
    ActiveRepairLateOriginalScan.bits d c j=rankKey E S T (s.bits+rowBits) j := by
  let x := (E).symm ⟨j,hj⟩
  have hc : Counter.value (RepairScan.counter c j)=(index s (d.n*d.b) (d.n*d.q) before after rows hw ha x).val := by
    change Counter.value (BinaryAddressTableData.row c j)=_
    rw [BinaryAddressTableData.row_rank c j (lt_of_lt_of_le hj hcounter)]
    exact (congrArg Fin.val ((E).apply_symm_apply ⟨j,hj⟩)).symm
  have hh := ActiveRepairLayoutKeysLate.destination (ActiveRepairLateOriginalScan.withCounter d (RepairScan.counter c j))
    (ActiveRepairLateOriginalScan.valid_counter d h _) s before after rows offset width rowBits he hw ha hp hf x hc hr
  change ActiveRepairLateOriginalScan.bits d c j = rankKey E S T (s.bits+rowBits) (E x).val at hh
  have hx : (E x).val=j := congrArg Fin.val ((E).apply_symm_apply ⟨j,hj⟩)
  rw [hx] at hh
  exact hh

end
end IntegerMultBounds.Machine.ActiveRepairLayoutKeysScanLate
