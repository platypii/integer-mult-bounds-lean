import IntegerMultBounds.Machine.CompactActualStageAllowance
import IntegerMultBounds.Machine.CompactReservationCutoff

/-! Actual scalar choices, the nonfallback cutoff and one global pad provide
all geometry/record prerequisites of the original-input stage producers.
No positive-row, guard-room or repair-width premise is supplied per node. -/
namespace IntegerMultBounds.Machine.CompactActualStageGeometry
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open CompactActualStageAllowance
open CompactGlobalRowPadding CompactGlobalReservation
open CompactScalarAllowances CompactReservationCutoff
open Sizes

structure Ready (s : Shape) (v : Stage s) (rows : ℕ) : Prop where
  guardPositive : 1≤s.guard
  guardRoom : s.guard+1≤s.chunk
  rowsPositive : 0<rows
  recordAllowance : s.bits+1≤s.payload
  fullAddressAllowance : s.bits+rows.log2+2≤s.payload
  repairGuard : s.guard+3≤s.chunk
  highestCapacity : 1≤s.H
  highestBefore : 1≤before v

 theorem eventually_ready (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload) (_hj : j≤depth m (d n))
      (v : Stage (actualShape n c m D payload)),
      Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j) := by
  filter_upwards [eventually_guard_fits,eventually_record_allowance] with n hk hrecord
  intro D payload j hcut hD hpayload hj v
  have hres := (cutoff_ready c m n D hc hm hcut).1.le
  have hp := hrecord D payload hD hpayload
  have hpos : 0<K n := by omega
  have ha := ActiveRepairLayoutGlobalAllowance.global_payload_allowance
    c m (d n) D (4*guardLog n+6) (K n) payload j (by omega) hpos hres hp
  have hg : 1≤(actualShape n c m D payload).guard := by
    change 1≤4*guardLog n+6
    omega
  refine ⟨hg,?_,rowsAt_positive c m (d n) (K n) j (by omega) hpos hj,?_,ha,?_,
    positive_H v hg,positive_before v⟩
  · change 4*guardLog n+6+1≤K n
    omega
  · have hh : (actualShape n c m D payload).bits+1≤
        (actualShape n c m D payload).bits+(rowsAt c m (d n) (K n) j).log2+2 := by omega
    exact hh.trans ha
  · change 4*guardLog n+6+3≤K n
    omega

end
end IntegerMultBounds.Machine.CompactActualStageGeometry
