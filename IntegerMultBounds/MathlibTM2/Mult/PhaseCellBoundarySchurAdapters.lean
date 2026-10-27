module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnscaledSolveTarget
public import IntegerMultBounds.NLogN.SchurBoundaryResidual

/-! Exact reduced solves and accuracy adapters for the retained Schur residual. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- The original principal-system solution solves the exact reduced boundary matrix. -/
theorem boundary_exact_schur_solves {ι : Type*} [DecidableEq ι]
    (M : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B)
    (μ : ℝ) (hμ : 0 < μ) (hM : DominatesOn M (I ∪ B) μ)
    (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves M I (R c) c)
    (x b : ι → ℝ) (hx : Solves M (I ∪ B) x b) :
    Solves (run M (I ∪ B) I.toList).1 B x (residual M I R b) := by
  intro i hi
  have hxS := (exact_schur M I B hIB μ hμ hM R hR b x hx).2 i hi
  have hident := schurOp_eq_run M I B hIB μ hμ hM R hR I.toList
    (Finset.toList_toFinset I) x i hi
  exact hident.symm.trans hxS

/-- Retained residual accuracy at the column target pays the boundary RHS budget. -/
theorem boundary_retained_rhs_budget (p target rhsExp N : ℕ) (hp : 0 < p) (e : ℝ)
    (he : 0 ≤ e)
    (herror : 8*(p : ℝ)*e ≤
      1/(2 : ℝ)^(recoveryTarget p (boundaryTableBits p target rhsExp N)+2)) :
    e ≤ 1/(2 : ℝ)^boundaryErrorBits p target rhsExp := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hsmall : e ≤ 8*(p : ℝ)*e := by nlinarith only [hpR,he]
  apply hsmall.trans (herror.trans ?_)
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_right₀ (by norm_num)
  unfold recoveryTarget boundaryTableBits
  omega

/-- The retained real residual is accurate in the complex norm used by the solve. -/
theorem boundary_retained_rhs_accuracy (q p target rhsExp N : ℕ) (hp : 0 < p)
    (z : GaussianInt) (c : ℝ) (hz : z.im = 0)
    (herror : 8*(p : ℝ)*|(value q z).re-c| ≤
      1/(2 : ℝ)^(recoveryTarget p (boundaryTableBits p target rhsExp N)+2)) :
    ‖value q z - (c : ℂ)‖ ≤ 1/(2 : ℝ)^boundaryErrorBits p target rhsExp := by
  have hreal : value q z = (((value q z).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · change (z.im : ℝ)/(2 : ℝ)^q = 0
      rw [hz]
      simp
  rw [hreal,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact boundary_retained_rhs_budget p target rhsExp N hp _ (abs_nonneg _) herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
