module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Exact real inequalities for the October 7 compact-control witness. These prove
the numerical and elementary analytic claims, not the algorithmic interfaces
whose costs the parameters are intended to satisfy.
-/

@[expose] public section

namespace IntegerMultBounds.Parameters
noncomputable section

def tau : ℝ := 1 - 123899714039 / 10 ^ 15
def sigma : ℝ := 1 - 418 / 10 ^ 12
def epsilon : ℝ := 1999 / 10000
def spacing : ℝ := 1 / 5
def beta : ℝ := 1 / 1000
def zeta : ℝ := 1 / 10000
def delta : ℝ := 1 / 10 ^ 6
def guardExponent : ℝ := 49961 / 10000
def lam : ℝ := 1 - 1671 / (4 * 10 ^ 12)
def lam' : ℝ := 1 - 167 / (4 * 10 ^ 11)
def kappa : ℝ := 83 / 10 ^ 12
def internalExponent : ℝ := tau + (1 - beta) * max (sigma - tau) 0
def leafExponent : ℝ := sigma + beta * (1 - sigma)
def reservationExponent : ℝ := max (1 - spacing) 0

/-- All parameter slacks used by the compact-control replacement, plus
the retained nonadjacent-layout and tight-Gaussian constraints. -/
def Admissible : Prop :=
  0 < tau ∧ tau < 1 ∧ 0 < sigma ∧ sigma < 1 ∧
  0 < spacing ∧ 0 < epsilon ∧ 0 < beta ∧ beta < 1 ∧ 0 < zeta ∧
  tau < lam ∧ sigma < lam ∧ internalExponent < lam ∧
  lam < lam' ∧ lam' < 1 ∧ leafExponent < lam' ∧ reservationExponent < lam' ∧
  guardExponent = 5 - 4 * beta + zeta ∧ epsilon * guardExponent < 1 ∧
  epsilon < 1 / 3 ∧ 0 < 1 - tau - epsilon * (1 - tau) ∧
  0 < 1 / 4 - delta - 5 * epsilon / 4 ∧
  0 < 1 - epsilon * (1 + spacing) ∧ 0 < 1 - delta - epsilon ∧
  0 < delta ∧ delta < 1 / 8 ∧ 0 < 1 - 2 * epsilon ∧
  0 < 1 / 4 - epsilon / 4 ∧ 0 < 1 / 2 - 3 * epsilon / 2 ∧
  0 < 1 - epsilon - epsilon * spacing ∧ 0 < epsilon * spacing ∧
  0 < 1 - epsilon ∧ 0 < kappa

theorem admissible : Admissible := by
  unfold Admissible
  repeat' apply And.intro
  all_goals norm_num [tau, sigma, epsilon, spacing, beta, zeta, delta,
    guardExponent, lam, lam', kappa, internalExponent, leafExponent, reservationExponent]

def margin : Fin 7 → ℝ := ![
  1 - epsilon * (1 + spacing),
  epsilon * spacing * (1 - tau),
  epsilon * (1 - lam'),
  (1 - tau) * (1 - epsilon),
  1 / 4 - delta - 5 * epsilon / 4,
  1 - delta - epsilon,
  epsilon]

theorem complex_deficit :
    (1 : ℝ) - 916333630984500000 / (58645352620000 * 15625) =
      14 / 3464399375 ∧
    (418 / 10 ^ 12 : ℝ) * (966 / 100) < 14 / 3464399375 := by
  norm_num

theorem complex_log_bound : Real.log 15625 < 966 / 100 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 966 / 100 by norm_num) 20
  have hsum : (15625 : ℝ) <
      ∑ i ∈ Finset.range 20, (966 / 100 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hsum.trans_le h

/-- The strict analytic branching-ratio inequality used by the complex recurrence. -/
theorem complex_branching_bound :
    (916333630984500000 / 58645352620000 : ℝ) < (15625 : ℝ) ^ sigma := by
  have hlog := complex_log_bound
  have hdef := complex_deficit
  have hpos : (0 : ℝ) < 418 / 10 ^ 12 := by norm_num
  have hlin := mul_lt_mul_of_pos_left hlog hpos
  have hexp := Real.add_one_le_exp (-(418 / 10 ^ 12 : ℝ) * Real.log 15625)
  have hr : (1 : ℝ) - 14 / 3464399375 <
      Real.exp (-(418 / 10 ^ 12 : ℝ) * Real.log 15625) := by
    linarith [hdef.2]
  have heq : (15625 : ℝ) ^ sigma =
      15625 * Real.exp (-(418 / 10 ^ 12 : ℝ) * Real.log 15625) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have : Real.log 15625 * sigma =
        Real.log 15625 + -(418 / 10 ^ 12 : ℝ) * Real.log 15625 := by
      unfold sigma
      ring
    rw [this, Real.exp_add, Real.exp_log (by norm_num)]
  rw [heq]
  nlinarith

end
end IntegerMultBounds.Parameters
