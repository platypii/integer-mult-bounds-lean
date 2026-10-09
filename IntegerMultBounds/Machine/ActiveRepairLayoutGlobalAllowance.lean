import IntegerMultBounds.Machine.CompactGlobalReservationRoles
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAllowance

/-! The original D-axis layout bounds repair addresses at every recursive
row depth after the single global pad. The row and within-row contributions
recombine to D*K, so neither a free row-header width nor a per-node address
allowance is needed. Precision and polynomial-record sizing remain explicit. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutGlobalAllowance
noncomputable section
open CompactGlobalRowPadding CompactGlobalReservation
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersData ActiveRepairLayoutRecordsAllowance

 theorem rows_log (c m d K j : ℕ) (hc : 0<c) (hK : 0<K) :
    (rowsAt c m d K j).log2≤rowAxes c m d*K+1 := by
  have hr := rowsAt_le_twice_original c m d K j hc hK
  have hh : rowsAt c m d K j≤2^(rowAxes c m d*K+1) := by
    simpa only [originalRows,pow_succ,Nat.mul_comm] using hr
  have hl := Nat.log_mono_right (b:=2) hh
  rw [←Nat.log2_eq_log_two,←Nat.log2_eq_log_two,Nat.log2_two_pow] at hl
  exact hl

 theorem complete_allowance (c m d D G K payload j : ℕ)
    (hc : 0<c) (hK : 0<K) (hD : reservedAxes c m d G K≤D) :
    (shape c m d D G K payload).bits+(rowsAt c m d K j).log2+2≤D*K+3 := by
  have hr := rows_log c m d K j hc hK
  have he := original_bits c m d D G K payload hK hD
  omega

 theorem path_complete_allowance (c m d D G K payload : ℕ)
    {q n : ℕ} {root v : RecursiveInterchangeLayout.Descriptor}
    (path : RecursiveInterchangeVolume.Path q c m root n v)
    (hc : 0<c) (hK : 0<K) (hD : reservedAxes c m d G K≤D)
    (hr : root.rows=initialRows c m d K) :
    (shape c m d D G K payload).bits+v.rows.log2+2≤D*K+3 := by
  rw [CompactGlobalReservationRoles.path_rows path hc hr]
  exact complete_allowance c m d D G K payload n hc hK hD

 theorem global_payload_allowance (c m d D G K payload j : ℕ)
    (hc : 0<c) (hK : 0<K) (hD : reservedAxes c m d G K≤D)
    (hrecord : D*K+3≤payload) :
    (shape c m d D G K payload).bits+(rowsAt c m d K j).log2+2≤payload :=
  (complete_allowance c m d D G K payload j hc hK hD).trans hrecord

 theorem global_dyadic_allowances (c m d D K payload j ell : ℕ) (P : ℝ)
    (p : Parameters (shape c m d D (4*ell+6) K payload)) (offset : ℕ)
    (input : Inputs (shape c m d D (4*ell+6) K payload) p offset (rowsAt c m d K j))
    (hc : 0<c) (hK : 8*ell+16≤K)
    (hD : reservedAxes c m d (4*ell+6) K≤D)
    (hrecord : D*K+3≤payload) (hsize : ((D*K+3:ℕ):ℝ)≤P^3)
    (hP : 0<P) (hn : (p.n:ℝ)≤P) (hell : P≤(2:ℝ)^ell)
    (hq : p.q=K) (hb : p.b=4*ell+6) :
    (geom input).addressBits+1≤payload ∧
      VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
        ((geom input).addressBits+1)≤1 ∧
      VaryingControlRepairDensity.lateDensity p.q p.b p.n*
        ((geom input).addressBits+1)≤1 := by
  have hpos : 0<K := by omega
  have ha := complete_allowance c m d D (4*ell+6) K payload j hc hpos hD
  apply dyadic_allowances input P ell hP hn hell (by simpa only [hq] using hK) hb
  · exact (Nat.cast_le.mpr ha).trans hsize
  · exact ha.trans hrecord

end
end IntegerMultBounds.Machine.ActiveRepairLayoutGlobalAllowance
