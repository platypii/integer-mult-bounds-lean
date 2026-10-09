import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Computable least high-digit row count for arbitrary-width pieces. The
selector is an exact natural ceiling logarithm; no guessed real parameter
or uncharged physical controller is asserted by these semantic theorems. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighRows

/-- Least number of paired high radix digits whose row count dominates D. -/
def rho (q D : ℕ) : ℕ := Nat.clog (q*q) D

def rowCount (q D : ℕ) : ℕ := q^(2*rho q D)

theorem square_base (q : ℕ) (hq : 2 ≤ q) : 1 < q*q := by nlinarith

theorem square_power (q n : ℕ) : q^(2*n) = (q*q)^n := by
  rw [pow_mul,pow_two]

/-- The selector is equivalently the first exponent accepted by the exact
integer comparison D≤q^(2n), suitable for a power-until controller. -/
theorem rho_le_iff (q D n : ℕ) (hq : 2 ≤ q) : rho q D ≤ n ↔ D ≤ q^(2*n) := by
  rw [square_power]
  exact Nat.clog_le_iff_le_pow (square_base q hq)

theorem dominates (q D : ℕ) (hq : 2 ≤ q) : D ≤ rowCount q D :=
  (rho_le_iff q D (rho q D) hq).mp le_rfl

theorem before_iff (q D n : ℕ) (hq : 2 ≤ q) : n < rho q D ↔ q^(2*n) < D := by
  rw [square_power]
  exact Nat.lt_clog_iff_pow_lt (square_base q hq)

theorem previous_lt (q D : ℕ) (hq : 2 ≤ q) (hr : 0 < rho q D) :
    q^(2*(rho q D-1)) < D :=
  (before_iff q D (rho q D-1) hq).mp (by omega)

/-- A concrete increasing-power scan which stops at its first accepted
comparison necessarily returns this exact computable selector. -/
theorem selected_unique (q D n : ℕ) (hq : 2 ≤ q) (hd : D ≤ q^(2*n))
    (hbefore : ∀ j < n, q^(2*j) < D) : n = rho q D := by
  have hn := (rho_le_iff q D n hq).mpr hd
  apply le_antisymm _ hn
  by_contra h
  have hs := hbefore (rho q D) (by omega)
  exact (not_lt_of_ge (dominates q D hq)) hs

@[simp] theorem rho_one (q : ℕ) : rho q 1 = 0 := Nat.clog_one_right _

theorem rho_zero_iff (q D : ℕ) (hq : 2 ≤ q) : rho q D = 0 ↔ D ≤ 1 := by
  simpa only [Nat.le_zero,mul_zero,pow_zero] using rho_le_iff q D 0 hq

theorem row_positive (q D : ℕ) (hq : 2 ≤ q) : 0 < rowCount q D :=
  Nat.pow_pos (by omega)

/-- Minimal selection overshoots by less than one paired-digit factor,
including the D=1 edge case where zero high digits are selected. -/
theorem row_lt (q D : ℕ) (hq : 2 ≤ q) (hD : 0 < D) : rowCount q D < q*q*D := by
  by_cases hr : rho q D = 0
  · simp only [rowCount,hr,mul_zero,pow_zero]
    have hb := square_base q hq
    nlinarith
  · have hp := previous_lt q D hq (by omega)
    have he : rho q D = (rho q D-1)+1 := by omega
    change q^(2*rho q D) < q*q*D
    rw [square_power,he,pow_succ]
    rw [square_power] at hp
    calc
      (q*q)^(rho q D-1)*(q*q) < D*(q*q) :=
        Nat.mul_lt_mul_of_pos_right hp (Nat.mul_pos (by omega) (by omega))
      _ = q*q*D := Nat.mul_comm _ _

/-- Concrete floor-log implementation: increment precisely when the target
is not already a power of the paired-digit radix. -/
theorem rho_log (q D : ℕ) (hq : 2 ≤ q) (hD : 0 < D) :
    rho q D = if (q*q)^(Nat.log (q*q) D) = D then Nat.log (q*q) D else Nat.log (q*q) D+1 := by
  have hb := square_base q hq
  have hlo : Nat.log (q*q) D ≤ rho q D := Nat.log_le_clog _ _
  have hpow := Nat.pow_log_le_self (q*q) (by omega : D ≠ 0)
  have hhi : rho q D ≤ Nat.log (q*q) D+1 :=
    (Nat.clog_le_iff_le_pow hb).mpr (Nat.lt_pow_succ_log_self hb D).le
  split_ifs with he
  · exact le_antisymm ((Nat.clog_le_iff_le_pow hb).mpr he.symm.le) hlo
  · have hne : rho q D ≠ Nat.log (q*q) D := by
      intro hh
      have hd : D ≤ (q*q)^(Nat.log (q*q) D) := by
        rw [← hh]
        exact Nat.le_pow_clog hb D
      exact he (le_antisymm hpow hd)
    omega

/-- The exact selector is the manuscript's real ceiling expression when
the target is W^k. Both natural computations therefore select the same rho. -/
theorem rho_manuscript (q W k : ℕ) (hq : 2 ≤ q) :
    rho q (W^k) = ⌈(k : ℝ)*Real.log W/(2*Real.log q)⌉₊ := by
  rw [rho,← Real.natCeil_logb_natCast]
  congr 1
  rw [Real.logb]
  simp only [Nat.cast_pow,Real.log_pow,Nat.cast_mul]
  rw [Real.log_mul (by exact_mod_cast (show q ≠ 0 by omega))
    (by exact_mod_cast (show q ≠ 0 by omega))]
  congr 1
  ring

theorem power_rows (q W k : ℕ) (hq : 2 ≤ q) (hW : 0 < W) :
    W^k ≤ rowCount q (W^k) ∧ rowCount q (W^k) < q*q*(W^k) :=
  ⟨dominates q (W^k) hq,row_lt q (W^k) hq (Nat.pow_pos hW)⟩

end IntegerMultBounds.Machine.ArbitraryWidthHighRows
