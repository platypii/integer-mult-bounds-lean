import IntegerMultBounds.Compact.Layout
import Mathlib.Data.Nat.Log

/-! The single global row padding of compact-control-layout.tex. The reserved
original row axes dominate the full recursive divisor. Every later fixed-role
split consumes one factor of that divisor without further padding. These are
layout/volume facts; construction of runtime descriptors is a separate machine. -/
namespace IntegerMultBounds.Machine.CompactGlobalRowPadding
open IntegerMultBounds.Compact.Layout (paddedRows)

def depth (m d : ℕ) := Nat.clog m d
def rowAxes (c m d : ℕ) := Nat.clog 2 c * Nat.clog m (2*d)
def originalRows (c m d K : ℕ) := 2^(rowAxes c m d*K)
def initialRows (c m d K : ℕ) := paddedRows (originalRows c m d K) (c^depth m d)
def rowsAt (c m d K j : ℕ) := initialRows c m d K/c^j

theorem divisor_le_original (c m d K : ℕ) (hK : 0 < K) :
    c^depth m d ≤ originalRows c m d K := by
  have hd : depth m d ≤ Nat.clog m (2*d) :=
    Nat.clog_mono_right m (by omega)
  calc
    c^depth m d ≤ (2^Nat.clog 2 c)^depth m d :=
      Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) c) _
    _ = 2^(Nat.clog 2 c*depth m d) := (pow_mul _ _ _).symm
    _ ≤ 2^(Nat.clog 2 c*Nat.clog m (2*d)) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hd)
    _ ≤ originalRows c m d K := by
      apply Nat.pow_le_pow_right (by decide)
      exact Nat.le_mul_of_pos_right _ hK

theorem initial_bounds (c m d K : ℕ) (hc : 0 < c) (hK : 0 < K) :
    originalRows c m d K ≤ initialRows c m d K ∧
    initialRows c m d K < originalRows c m d K+c^depth m d ∧
    initialRows c m d K ≤ 2*originalRows c m d K ∧
    c^depth m d ∣ initialRows c m d K :=
  Compact.Layout.padding_bounds _ _ (pow_pos hc _) (divisor_le_original c m d K hK)

theorem initial_positive (c m d K : ℕ) (hc : 0 < c) (hK : 0 < K) :
    0 < initialRows c m d K :=
  lt_of_lt_of_le (pow_pos (by decide) _) (initial_bounds c m d K hc hK).1

/-- Divisibility at every actual depth follows from the one original pad. -/
theorem rowsAt_divisible (c m d K j : ℕ) (hc : 0 < c) (hK : 0 < K)
    (hj : j ≤ depth m d) : c^(depth m d-j) ∣ rowsAt c m d K j := by
  obtain ⟨t,ht⟩ := (initial_bounds c m d K hc hK).2.2.2
  unfold rowsAt
  rw [ht,show c^depth m d = c^(depth m d-j)*c^j by
    rw [← pow_add,Nat.sub_add_cancel hj]]
  have he : c^(depth m d-j)*c^j*t = (c^(depth m d-j)*t)*c^j := by ring
  rw [he,Nat.mul_div_cancel _ (pow_pos hc _)]
  exact dvd_mul_right _ _

theorem rowsAt_positive (c m d K j : ℕ) (hc : 0 < c) (hK : 0 < K)
    (hj : j ≤ depth m d) : 0 < rowsAt c m d K j := by
  have hd : c^j ∣ initialRows c m d K :=
    dvd_trans (pow_dvd_pow c hj) (initial_bounds c m d K hc hK).2.2.2
  exact Nat.div_pos (Nat.le_of_dvd (initial_positive c m d K hc hK) hd) (pow_pos hc _)

theorem split_divides (c m d K j : ℕ) (hc : 0 < c) (hK : 0 < K)
    (hj : j < depth m d) : c ∣ rowsAt c m d K j := by
  exact dvd_trans (dvd_pow_self c (by omega : depth m d-j ≠ 0))
    (rowsAt_divisible c m d K j hc hK (by omega))

theorem padded_eq_of_dvd (r c : ℕ) (h : c ∣ r) : paddedRows r c = r := by
  simp [paddedRows,Nat.mod_eq_zero_of_dvd h]

theorem no_repadding (c m d K j : ℕ) (hc : 0 < c) (hK : 0 < K)
    (hj : j < depth m d) : paddedRows (rowsAt c m d K j) c = rowsAt c m d K j :=
  padded_eq_of_dvd _ _ (split_divides c m d K j hc hK hj)

theorem next_rows (c m d K j : ℕ) : rowsAt c m d K j/c = rowsAt c m d K (j+1) := by
  simp only [rowsAt,Nat.div_div_eq_div_mul,pow_succ]

theorem rowsAt_mul (c m d K j : ℕ) (hc : 0 < c) (hK : 0 < K)
    (hj : j ≤ depth m d) : rowsAt c m d K j*c^j = initialRows c m d K := by
  exact Nat.div_mul_cancel (dvd_trans (pow_dvd_pow c hj)
    (initial_bounds c m d K hc hK).2.2.2)

/-- Complete original-record volume, with no discarded spectator fields. -/
theorem role_volume (c m d K j l : ℕ) (hc : 0 < c) (hK : 0 < K)
    (hj : j < depth m d) : rowsAt c m d K (j+1)*l*c = rowsAt c m d K j*l := by
  rw [← next_rows]
  calc
    _ = (rowsAt c m d K j/c*c)*l := by ring
    _ = _ := by rw [Nat.div_mul_cancel (split_divides c m d K j hc hK hj)]

theorem rowsAt_le_initial (c m d K j : ℕ) : rowsAt c m d K j ≤ initialRows c m d K :=
  Nat.div_le_self _ _

theorem rowsAt_le_twice_original (c m d K j : ℕ) (hc : 0 < c) (hK : 0 < K) :
    rowsAt c m d K j ≤ 2*originalRows c m d K :=
  (rowsAt_le_initial c m d K j).trans (initial_bounds c m d K hc hK).2.2.1

end IntegerMultBounds.Machine.CompactGlobalRowPadding
