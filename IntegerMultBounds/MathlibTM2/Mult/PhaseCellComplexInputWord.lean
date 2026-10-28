module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealInputWord

/-! The ordinary complex p-grid input encoding and its exact retraction law. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.ShortConv

noncomputable def complexInputWord (p : ℕ) (z : ℂ) : GaussianInt :=
  ⟨rho0 ((2 : ℝ)^p*z.re),rho0 ((2 : ℝ)^p*z.im)⟩

theorem complexInputWord_value (p : ℕ) (z : ℂ) :
    value p (complexInputWord p z) = rhoC p z := rfl

theorem complexInputWord_grid (p : ℕ) (z : GaussianInt) : complexInputWord p (value p z) = z := by
  have hr := congrArg (fun w : GaussianInt => w.re) (realInputWord_grid p z.re)
  have hi := congrArg (fun w : GaussianInt => w.re) (realInputWord_grid p z.im)
  exact Zsqrtd.ext hr hi

noncomputable def gridInput {s : ℕ} (p : ℕ) (v : ZMod s → ℂ) : ZMod s → GaussianInt :=
  fun i => complexInputWord p (v i)

theorem gridInput_norm {s : ℕ} [NeZero s] (p : ℕ) (v : ZMod s → ℂ) :
    ‖fun i => value p (gridInput p v i)‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro i
  exact (norm_rhoC_le p (v i)).trans (norm_le_pi_norm v i)

theorem gridInput_error {s : ℕ} [NeZero s] (p : ℕ) (v : ZMod s → ℂ) :
    ‖(fun i => value p (gridInput p v i))-v‖ ≤ 2/(2 : ℝ)^p := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  exact norm_rhoC_sub_le_two p (v i)

theorem gridInput_grid {s : ℕ} (p : ℕ) (F : ZMod s → GaussianInt) :
    gridInput p (fun i => value p (F i)) = F := by
  funext i
  exact complexInputWord_grid p (F i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
