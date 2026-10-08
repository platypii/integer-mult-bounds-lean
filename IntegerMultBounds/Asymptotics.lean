import IntegerMultBounds.Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Strict exponent gaps absorb every fixed logarithmic power. These are
analytic bounds on functions, not assumptions about a machine's execution. -/

namespace IntegerMultBounds
open Filter Asymptotics

theorem log_power_absorbed {a b : ℝ} (hab : a < b) (k : ℝ) :
    (fun p : ℝ => Real.log p ^ k * p ^ a) =o[atTop] (fun p => p ^ b) := by
  have h := (isLittleO_log_rpow_rpow_atTop k (sub_pos.mpr hab)).mul_isBigO
    (isBigO_refl (fun p : ℝ => p ^ a) atTop)
  apply h.congr' (Filter.Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
  rw [← Real.rpow_add hp]
  congr 1
  ring

theorem assembly_log_absorbed (i : Fin 7) (k : ℝ) :
    (fun p : ℝ => Real.log p ^ k * p ^ (1 - Parameters.margin i))
      =o[atTop] (fun p => p ^ (1 - Parameters.kappa)) := by
  apply log_power_absorbed
  linarith [Parameters.margin_strict i]

/-- A volume-normalized recurrence estimate for every finite depth. The leaf
cost `L` and per-node overhead `A` are explicit. -/
theorem recurrence_bound (F : ℕ → ℝ) (b q L A : ℝ)
    (hb : 0 ≤ b) (hq : 0 ≤ q) (hA : 0 ≤ A)
    (hbase : F 0 ≤ L)
    (hstep : ∀ k, F (k + 1) ≤ b * F k + A * q ^ (k + 1)) :
    ∀ k, F k ≤ b ^ k * L + A * k * (max b q) ^ k := by
  intro k
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    have hm : 0 ≤ max b q := le_trans hb (le_max_left _ _)
    have hp : 0 ≤ (max b q) ^ k := pow_nonneg hm k
    have hqpow : q ^ (k + 1) ≤ (max b q) ^ (k + 1) :=
      pow_le_pow_left₀ hq (le_max_right _ _) _
    have hbpow : b * (max b q) ^ k ≤ (max b q) ^ (k + 1) := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hp
    calc
      F (k + 1) ≤ b * F k + A * q ^ (k + 1) := hstep k
      _ ≤ b * (b ^ k * L + A * k * (max b q) ^ k) +
          A * (max b q) ^ (k + 1) := by gcongr
      _ ≤ b ^ (k + 1) * L + A * (k + 1) * (max b q) ^ (k + 1) := by
        have hh := mul_le_mul_of_nonneg_left hbpow
          (show 0 ≤ A * (k : ℝ) by positivity)
        rw [pow_succ' b]
        nlinarith
      _ = b ^ (k + 1) * L + A * (↑(k + 1) : ℝ) * (max b q) ^ (k + 1) := by
        push_cast
        rfl

end IntegerMultBounds
