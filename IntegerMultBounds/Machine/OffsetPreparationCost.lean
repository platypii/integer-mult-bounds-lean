import Mathlib.Analysis.SpecificLimits.Normed

/-! Polynomial control preparation is absorbed by prime-power fiber width.
These analytic bounds do not supply a physical preparation program. -/
namespace IntegerMultBounds.Machine.OffsetPreparationCost

open Filter Asymptotics

/-- Every fixed polynomial degree is negligible compared with the radix width. -/
theorem polynomial_small (q k : ℕ) (hq : 2 ≤ q) :
    (fun b : ℕ => (b : ℝ)^k) =o[atTop] (fun b => (q : ℝ)^b) := by
  apply isLittleO_pow_const_const_pow_of_one_lt
  exact_mod_cast (show 1 < q by omega)

/-- A proved polynomial bound on a physical preparation cost yields the bound
needed to absorb that cost into each nonempty target fiber. -/
theorem preparation_bigO (q k : ℕ) (hq : 2 ≤ q) (cost : ℕ → ℝ)
    (hcost : cost =O[atTop] (fun b : ℕ => (b : ℝ)^k)) :
    cost =O[atTop] (fun b => (q : ℝ)^b) :=
  hcost.trans (polynomial_small q k hq).isBigO

/-- Suffix lengths may vary arbitrarily, provided each record is nonempty. -/
theorem preparation_fiber_bigO (q k : ℕ) (hq : 2 ≤ q) (cost : ℕ → ℝ)
    (hcost : cost =O[atTop] (fun b : ℕ => (b : ℝ)^k))
    (B : ℕ → ℕ) (hB : ∀ b, 0 < B b) :
    cost =O[atTop] (fun b => (q : ℝ)^b * (B b : ℝ)) := by
  apply (preparation_bigO q k hq cost hcost).trans
  apply isBigO_of_le' (c := 1)
  intro b
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  rw [one_mul]
  have hb : (1 : ℝ) ≤ (B b : ℝ) := by exact_mod_cast hB b
  exact le_mul_of_one_le_right (by positivity) hb

end IntegerMultBounds.Machine.OffsetPreparationCost
