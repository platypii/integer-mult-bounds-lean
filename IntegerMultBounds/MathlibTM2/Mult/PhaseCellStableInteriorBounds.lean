module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealCouplingField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
public import IntegerMultBounds.NLogN.PhaseCellBoundary

/-! Stability bounds for the real interior output, independent of the arithmetic precision. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

/-- A common dyadic bound for an approximate real interior solve. -/
def stableInteriorExponent (p rhsExp : ℕ) : ℕ := rhsExp+8*p+1

theorem stableSolve_norm {s t p u q rhsExp : ℕ} [NeZero s]
    (hp : 0 < p) (active core : Finset (ZMod s)) (hcore : core ⊆ active)
    (hdom : SchurDominance.DominatesOn (PhaseCellMatrix.realMatrix s t p u)
      Finset.univ (1/(8*(p : ℝ))))
    (C D : ZMod s → GaussianInt) (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (PhaseCellMatrix.realMatrix s t p u) active x
      (fun i => (value q (C i)).re))
    (herror : PhaseCellInterface.ErrorOn core (fun i => (value q (D i)).re) x 1) :
    ∀ i ∈ core, ‖value q (realPartWord (D i))‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp := by
  intro i hi
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hAI := SchurDominance.dominates_mono _ Finset.univ active _ (Finset.subset_univ active) hdom
  have hxi := SchurDominance.solves_bound _ active _ hμ hAI x _ hx ((2 : ℝ)^rhsExp)
    (fun i _ => (Complex.abs_re_le_norm _).trans (hC i)) i (hcore hi)
  have hx' : |x i| ≤ 8*(p : ℝ)*(2 : ℝ)^rhsExp := by
    simpa only [div_div_eq_mul_div,div_one,mul_comm] using hxi
  have herr : |(value q (D i)).re-x i| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using herror i hi
  have hpPow : (8*(p : ℝ)) ≤ (2 : ℝ)^(8*p) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := 8*p)).le
  have hb : (1 : ℝ) ≤ (2 : ℝ)^rhsExp := one_le_pow₀ (by norm_num)
  have hg : (1 : ℝ) ≤ (2 : ℝ)^(8*p) := one_le_pow₀ (by norm_num)
  rw [value_realPartWord_norm]
  have htriangle := abs_add_le ((value q (D i)).re-x i) (x i)
  rw [sub_add_cancel] at htriangle
  calc |(value q (D i)).re| ≤ 1+8*(p : ℝ)*(2 : ℝ)^rhsExp := by linarith
    _ ≤ (2 : ℝ)^rhsExp+(2 : ℝ)^(8*p)*(2 : ℝ)^rhsExp :=
      add_le_add hb (mul_le_mul_of_nonneg_right hpPow (by positivity))
    _ ≤ (2 : ℝ)^(8*p)*(2 : ℝ)^rhsExp+(2 : ℝ)^(8*p)*(2 : ℝ)^rhsExp := by
      have hmul : (2 : ℝ)^rhsExp ≤ (2 : ℝ)^(8*p)*(2 : ℝ)^rhsExp := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hg
          (show (0 : ℝ) ≤ (2 : ℝ)^rhsExp by positivity)
      exact add_le_add hmul le_rfl
    _ = (2 : ℝ)^stableInteriorExponent p rhsExp := by
      rw [stableInteriorExponent,pow_succ,pow_add]
      ring

theorem stableInterior_norm {s t p u q rhsExp target : ℕ} [NeZero s]
    (hp : 0 < p) (I : Finset (ZMod s))
    (hdom : SchurDominance.DominatesOn (PhaseCellMatrix.realMatrix s t p u)
      Finset.univ (1/(8*(p : ℝ))))
    (C D : ZMod s → GaussianInt) (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (PhaseCellMatrix.realMatrix s t p u) I x
      (fun i => (value q (C i)).re))
    (herror : PhaseCellInterface.ErrorOn I (fun i => (value q (D i)).re) x (1/(2 : ℝ)^target)) :
    ∀ i ∈ I, ‖value q (realPartWord (D i))‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp := by
  apply stableSolve_norm hp I I (Finset.Subset.refl I) hdom C D hC x hx
  intro i hi
  apply (herror i hi).trans
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
