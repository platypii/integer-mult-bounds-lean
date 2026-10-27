module

public import IntegerMultBounds.NLogN.PhaseCellBoundarySolve
public import IntegerMultBounds.NLogN.PhaseCellBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStableInteriorBounds

/-! Stable magnitude of the original solution, before boundary reduction. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance

/-- Bound a complex solution through the two real solves of a dominant matrix. -/
theorem dominant_complex_solution_bound {ι : Type*} [DecidableEq ι]
    (M : Matrix ι ι ℝ) (S : Finset ι) (p rhsExp : ℕ) (hp : 0 < p)
    (hM : DominatesOn M S (1/(8*(p : ℝ)))) (x b : ι → ℂ)
    (hre : Solves M S (fun i => (x i).re) (fun i => (b i).re))
    (him : Solves M S (fun i => (x i).im) (fun i => (b i).im))
    (hb : ∀ i ∈ S, ‖b i‖ ≤ (2 : ℝ)^rhsExp) :
    ∀ i ∈ S, ‖x i‖ ≤ 16*(p : ℝ)*(2 : ℝ)^rhsExp := by
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  intro i hi
  have hr := solves_bound M S _ hμ hM _ _ hre ((2 : ℝ)^rhsExp)
    (fun j hj => (Complex.abs_re_le_norm _).trans (hb j hj)) i hi
  have hm := solves_bound M S _ hμ hM _ _ him ((2 : ℝ)^rhsExp)
    (fun j hj => (Complex.abs_im_le_norm _).trans (hb j hj)) i hi
  rw [div_div_eq_mul_div,div_one] at hr hm
  have hn := Complex.norm_le_abs_re_add_abs_im (x i)
  nlinarith only [hr,hm,hn]

/-- The original phase-cell solution has a stable magnitude independent of the
larger retained residual and its normalization scale. -/
theorem phaseCell_exact_solution_bound (s t : ℕ) [NeZero s] [NeZero t]
    (hst : s < t) {α d : ℝ} (hα : 0 < α) (p u rhsExp : ℕ)
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (x b : ZMod s → ℂ)
    (hre : Solves (realMatrix s t p u) Finset.univ (fun i => (x i).re) (fun i => (b i).re))
    (him : Solves (realMatrix s t p u) Finset.univ (fun i => (x i).im) (fun i => (b i).im))
    (hb : ∀ i, ‖b i‖ ≤ (2 : ℝ)^rhsExp) :
    ∀ i, ‖x i‖ ≤ 16*(p : ℝ)*(2 : ℝ)^rhsExp := by
  intro i
  exact dominant_complex_solution_bound _ Finset.univ p rhsExp (by omega)
    (matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget) x b hre him
    (fun j _ => hb j) i (Finset.mem_univ i)

/-- Accurate boundary output fits the recovery stage's existing stable magnitude. -/
theorem boundary_computed_solution_magnitude (p rhsExp target : ℕ) (hp : 0 < p)
    (y x : ℂ) (hx : ‖x‖ ≤ 16*(p : ℝ)*(2 : ℝ)^rhsExp)
    (hy : ‖y-x‖ ≤ 3/(2 : ℝ)^target) :
    ‖y‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp := by
  have hpPow : (p : ℝ) ≤ (2 : ℝ)^p := by exact_mod_cast (Nat.lt_two_pow_self (n := p)).le
  have hρ : (1 : ℝ) ≤ 2^rhsExp := one_le_pow₀ (by norm_num)
  have hP : (1 : ℝ) ≤ 2^p := one_le_pow₀ (by norm_num)
  have he : 3/(2 : ℝ)^target ≤ 3 := by
    exact (div_le_iff₀ (by positivity)).mpr (by nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := target)])
  have hcoeff : 16*(p : ℝ)+3 ≤ (2 : ℝ)^(8*p+1) := by
    calc
      _ ≤ 32*(2 : ℝ)^p := by nlinarith only [hpPow,hP]
      _ = (2 : ℝ)^(p+5) := by rw [pow_add]; norm_num; ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hn := norm_le_norm_sub_add y x
  calc
    ‖y‖ ≤ 16*(p : ℝ)*(2 : ℝ)^rhsExp+3 := by linarith
    _ ≤ (16*(p : ℝ)+3)*(2 : ℝ)^rhsExp := by nlinarith only [hρ]
    _ ≤ (2 : ℝ)^(8*p+1)*(2 : ℝ)^rhsExp := mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; unfold stableInteriorExponent; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
