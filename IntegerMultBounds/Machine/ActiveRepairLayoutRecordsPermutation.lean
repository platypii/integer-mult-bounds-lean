import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsShape

/-! Concrete packed actual and ideal operations move whole records and retain
all bit positions inside them. Repair uses the address-only permutation. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPermutation
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairLayoutRecordsShape ActiveRepairLayoutPermutation
variable (s : Shape) (q b n before after rows rho offset width : ℕ)
variable (side : ActiveRepairRankHeadersData.SourceSide) (hq : 1≤q)
variable (x : RecordAddress s (n*b) (n*q) before after rows) (r : Fin s.payload)

theorem early_actual :
    earlyActual s q b n before after rows rho offset width side hq
      (cell s (n*b) (n*q) before after rows x r)=
    cell s (n*b) (n*q) before after rows
      (earlyActual (addressShape s) q b n before after rows rho offset width side hq x) r := by
  rfl

theorem early_ideal :
    earlyIdeal s q b n before after rows rho offset width side hq
      (cell s (n*b) (n*q) before after rows x r)=
    cell s (n*b) (n*q) before after rows
      (earlyIdeal (addressShape s) q b n before after rows rho offset width side hq x) r := by
  rfl

theorem early_bad :
    earlyBad s q b n before after rows rho offset width side hq
      (cell s (n*b) (n*q) before after rows x r) ↔
    earlyBad (addressShape s) q b n before after rows rho offset width side hq x := Iff.rfl

theorem late_actual :
    lateActual s q b n before after rows rho offset width side hq
      (cell s (n*b) (n*q) before after rows x r)=
    cell s (n*b) (n*q) before after rows
      (lateActual (addressShape s) q b n before after rows rho offset width side hq x) r := by
  rfl

theorem late_ideal :
    lateIdeal s q b n before after rows rho offset width side hq
      (cell s (n*b) (n*q) before after rows x r)=
    cell s (n*b) (n*q) before after rows
      (lateIdeal (addressShape s) q b n before after rows rho offset width side hq x) r := by
  rfl

theorem late_bad :
    lateBad s q b n before after rows rho offset width side hq
      (cell s (n*b) (n*q) before after rows x r) ↔
    lateBad (addressShape s) q b n before after rows rho offset width side hq x := Iff.rfl

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPermutation
