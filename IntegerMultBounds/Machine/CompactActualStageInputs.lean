import IntegerMultBounds.Machine.CompactActualStageGeometry
import IntegerMultBounds.Machine.ActivePrefixStageFullData

/-! Actual scalar/row readiness fills the original-input physical stage
record. Its repair allowances follow at density constant one for both source
orders; no derived descriptor word or per-node width allowance is supplied. -/
namespace IntegerMultBounds.Machine.CompactActualStageInputs
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open CompactActualStageGeometry CompactActualStageAllowance
open CompactGlobalRowPadding CompactReservationCutoff
open Sizes
open ActivePrefixStageHeadersData (Order)

def inputs {s : Shape} (v : Stage s) (rows : ℕ) (h : Ready s v rows) :
    ActivePrefixStageFullData.Inputs s where
  stage := v
  rows := rows
  hG := h.guardPositive
  hGK := h.guardRoom
  hr := h.rowsPositive
  hrecord := h.recordAllowance

 theorem eventually_allowances (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D payload j : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hpayload : 6*b n*2^ℓ n≤payload)
      (v : Stage (actualShape n c m D payload))
      (h : Ready (actualShape n c m D payload) v (rowsAt c m (d n) (K n) j)) (order : Order),
      let input := inputs v (rowsAt c m (d n) (K n) j) h
      let ds := ActivePrefixStageFullData.descriptors order input
      (ActiveRepairLayoutRecordsHeadersData.geom ds).addressBits+1≤payload ∧
        VaryingControlRepairDensity.earlyDensity (K n) (4*CompactScalarAllowances.guardLog n+6) (v.f-1)*
          ((ActiveRepairLayoutRecordsHeadersData.geom ds).addressBits+1)≤1 ∧
        VaryingControlRepairDensity.lateDensity (K n) (4*CompactScalarAllowances.guardLog n+6) (v.f-1)*
          ((ActiveRepairLayoutRecordsHeadersData.geom ds).addressBits+1)≤1 := by
  filter_upwards [CompactActualStageAllowance.eventually_allowances] with n hn
  intro D payload j hcut hD hpayload v h order
  exact hn c m D payload j (by omega) hD
    (cutoff_ready c m n D hc hm hcut).1.le hpayload v h.guardPositive h.guardRoom
    (ActivePrefixStageHeadersData.offset order v)
    (ActivePrefixStageFullData.descriptors order (inputs v (rowsAt c m (d n) (K n) j) h))

end
end IntegerMultBounds.Machine.CompactActualStageInputs
