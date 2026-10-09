import IntegerMultBounds.Machine.CompactScalarAllowances
import IntegerMultBounds.Machine.ActiveRepairLayoutGlobalAllowance
import IntegerMultBounds.Machine.ActivePrefixStageParameters

/-! Every actual original-slot stage uses density constant one. Complete
repair address width, guard size and selected-count allowances follow from
multiplier scalar choices and once-padded descendant rows, rather than free
consumer-width hypotheses. Reservation-axis fit remains the nonfallback
condition; the polynomial-record width is the original input contract. -/
namespace IntegerMultBounds.Machine.CompactActualStageAllowance
noncomputable section
open Sizes TimeBound
open CompactGlobalRowPadding CompactGlobalReservation CompactScalarAllowances
open ActivePrefixStageParameters
open ActivePrefixEarlySequenceOriginalInputs (Inputs)
open ActiveRepairLayoutRecordsHeadersData (geom)

def actualShape (n c m D payload : ℕ) :=
  shape c m (d n) D (4*guardLog n+6) (K n) payload

 theorem eventually_allowances : ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (c m D payload j : ℕ) (_hc : 0<c) (_hD : D≤d n)
      (_hreserved : reservedAxes c m (d n) (4*guardLog n+6) (K n)≤D)
      (_hpayload : 6*b n*2^ℓ n≤payload)
      (v : Stage (actualShape n c m D payload))
      (hG : 1≤(actualShape n c m D payload).guard)
      (hGK : (actualShape n c m D payload).guard+1≤(actualShape n c m D payload).chunk)
      (offset : ℕ)
      (input : Inputs (actualShape n c m D payload) (parameters v hG hGK) offset
        (rowsAt c m (d n) (K n) j)),
      (geom input).addressBits+1≤payload ∧
        VaryingControlRepairDensity.earlyDensity (K n) (4*guardLog n+6) (v.f-1)*
          ((geom input).addressBits+1)≤1 ∧
        VaryingControlRepairDensity.lateDensity (K n) (4*guardLog n+6) (v.f-1)*
          ((geom input).addressBits+1)≤1 := by
  filter_upwards [eventually_guard_fits,eventually_record_allowance] with n hk hp
  intro c m D payload j hc hD hreserved hpayload v hG hGK offset input
  have hrecord := hp D payload hD hpayload
  have hsize := original_axis_cubic n D hD
  have hn : ((v.f-1:ℕ):ℝ)≤precision n :=
    selected_count n v.f v.widthFits
  exact ActiveRepairLayoutGlobalAllowance.global_dyadic_allowances
    c m (d n) D (K n) payload j (guardLog n) (precision n)
    (parameters v hG hGK) offset input hc hk hreserved hrecord hsize
    (precision_pos n) hn (precision_dyadic n) rfl rfl

end
end IntegerMultBounds.Machine.CompactActualStageAllowance
