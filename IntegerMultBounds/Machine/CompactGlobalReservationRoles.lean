import IntegerMultBounds.Machine.CompactGlobalReservation
import IntegerMultBounds.Machine.CompactGadgetReservationData
import IntegerMultBounds.Machine.RecursiveInterchangeVolume

/-! The global once-padded row range supplies every recursive physical role
reservation. Its real padding/splitting machine adds no rows at a node, and
its cost and complete role volume use that node's current logical volume. -/
namespace IntegerMultBounds.Machine.CompactGlobalReservationRoles
noncomputable section
open CompactGlobalRowPadding
open CompactGadgetReservationData
open CompactGadgetReservationShape
open IntegerMultBounds.Compact.Layout (paddedRows)
open RecursiveInterchangeLayout (volume role)
variable {a c m d K j : ℕ}

theorem rowCount_eq (hc : 0 < c) (hK : 0 < K) (hj : j < depth m d) :
    rowCount (rowsAt c m d K j) c = rowsAt c m d K (j+1) := by
  unfold rowCount
  rw [no_repadding c m d K j hc hK hj,next_rows]

/-- The reservation endpoint's concrete role word has exactly one c-th of
its input's full record volume, with no extra per-node padding coefficient. -/
theorem exact_role_volume (l : ℕ) (hc : 0 < c) (hK : 0 < K) (hj : j < depth m d) :
    volume a (role (CompactRowHeaders.descriptor (paddedRows (rowsAt c m d K j) c) l) c)*c =
      rowsAt c m d K j*l := by
  rw [role_size,rowCount_eq hc hK hj]
  exact CompactGlobalRowPadding.role_volume c m d K j l hc hK hj

theorem exact_rectangle_volume (s : Shape) (n : ℕ) (hn : n ≤ s.axes) (f : Front)
    (hc : 0 < c) (hK : 0 < K) (hj : j < depth m d) :
    RadixRangePadding.volume (s.prefixRange (rowCount (rowsAt c m d K j) c) f)
      (2^s.width n) (s.gap n f) (s.suffix n)*c = rowsAt c m d K j*s.recordWidth := by
  rw [s.rectangle_volume n _ hn f,rowCount_eq hc hK hj]
  exact CompactGlobalRowPadding.role_volume c m d K j s.recordWidth hc hK hj

theorem budget_linear (l : ℕ) (hc : 0 < c) (hK : 0 < K) (hj : j < depth m d)
    (hl : 0 < l) :
    CompactRowReservationRun.budget c (rowsAt c m d K j) l ≤
      CompactRowReservationBudget.constant c*(rowsAt c m d K j*l) := by
  have h := CompactRowReservationBudget.linear c (rowsAt c m d K j) l hc
    (rowsAt_positive c m d K j hc hK (by omega)) hl
  rwa [no_repadding c m d K j hc hK hj] at h

/-- Actual original-header reservation, paid against the current input word.
The fixed c-role program is independent of runtime global depth. -/
theorem runs (ha : 2 ≤ a) (rs ls : List Bool) (l : ℕ)
    (x : Fin (1*rowsAt c m d K j*l) → Bool)
    (hr : Counter.value rs = rowsAt c m d K j) (hl : Counter.value ls = l)
    (cr : GrowingCounterData.Canonical rs) (cl : GrowingCounterData.Canonical ls)
    (hL : 0 < l) (hc : 0 < c) (hK : 0 < K) (hj : j < depth m d) :
    HoareTime (CompactRowReservationRun.program ha c)
      (fun w => w = CompactRowReservationPlacement.bank (CompactRowReservationData.original x)
        (CompactRowReservationRun.emptyPayload (c := c)) rs ls none none)
      (fun w => w = CompactRowReservationEndpoint.final hc x rs ls)
      (CompactRowReservationBudget.constant c*(rowsAt c m d K j*l)) :=
  (CompactRowReservationRun.runs ha c rs ls _ l x hr hl cr cl
    (rowsAt_positive c m d K j hc hK (by omega)) hL hc).consequence
      (fun _ h => h) (fun _ h => h) (budget_linear l hc hK hj hL)

/-- The arithmetic rows are also the rows of an actual descriptor-child path;
no separate current-node divisibility hypothesis is needed. -/
theorem path_rows {q n : ℕ} {root v : RecursiveInterchangeLayout.Descriptor}
    (path : RecursiveInterchangeVolume.Path q c m root n v)
    (hc : 0 < c) (hr : root.rows = initialRows c m d K) : v.rows = rowsAt c m d K n := by
  unfold rowsAt
  rw [← hr,← path.rows_mul,Nat.mul_div_cancel _ (pow_pos hc _)]

theorem path_divisible {q n : ℕ} {root v : RecursiveInterchangeLayout.Descriptor}
    (path : RecursiveInterchangeVolume.Path q c m root n v)
    (hc : 0 < c) (hK : 0 < K) (hr : root.rows = initialRows c m d K)
    (hn : n ≤ depth m d) : c^(depth m d-n) ∣ v.rows := by
  rw [path_rows path hc hr]
  exact rowsAt_divisible c m d K n hc hK hn

/-- A power-width piece determines its own legal depth, rather than carrying
an unrelated bound at each node. -/
theorem path_divisible_of_width {q n k : ℕ} {root v : RecursiveInterchangeLayout.Descriptor}
    (path : RecursiveInterchangeVolume.Path q c m root n v)
    (hc : 0 < c) (hm : 1 < m) (hK : 0 < K) (hr : root.rows = initialRows c m d K)
    (hw : root.width = m^k) (hk : k ≤ depth m d) : c^(depth m d-n) ∣ v.rows :=
  path_divisible path hc hK hr ((path.depth_bound hm hw).trans hk)

theorem path_rows_bounded {q n : ℕ} {root v : RecursiveInterchangeLayout.Descriptor}
    (path : RecursiveInterchangeVolume.Path q c m root n v)
    (hc : 0 < c) (hK : 0 < K) (hr : root.rows = initialRows c m d K) :
    v.rows ≤ 2*originalRows c m d K := by
  rw [path_rows path hc hr]
  exact rowsAt_le_twice_original c m d K n hc hK

end
end IntegerMultBounds.Machine.CompactGlobalReservationRoles
