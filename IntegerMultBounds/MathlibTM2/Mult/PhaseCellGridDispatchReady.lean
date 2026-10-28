module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridFamilyInverseBatch

/-! The descriptor frame is shared; p-grid readiness supplies the actual unit input bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

structure GridDispatchReady {s A : ℕ} [NeZero s] (p l t : ℕ) (d : ℝ)
    (r : FamilyDispatchInput s A) : Prop extends FamilyDispatchFrame p l t d r where
  inputBound : ∀ F ∈ r.inputs, ∀ i, ‖value p (F i)‖ ≤ 1

theorem value_norm_mono_precision {p q : ℕ} (hpq : p ≤ q) (z : GaussianInt) :
    ‖value q z‖ ≤ ‖value p z‖ := by
  simp only [value_eq_grid,norm_div,norm_pow,RCLike.norm_two]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hpq)

theorem GridDispatchReady.raw {s A p l t : ℕ} [NeZero s] {d : ℝ}
    {r : FamilyDispatchInput s A} (hr : GridDispatchReady p l t d r) :
    FamilyDispatchReady p l t d r := by
  have hpq : p ≤ r.precision p l t := by
    simp only [FamilyDispatchInput.precision,executionPrecision,←inverseExecutionExponent_eq]
    dsimp [inverseExecutionExponent]
    omega
  refine { toFamilyDispatchFrame := hr.toFamilyDispatchFrame, inputBound := ?_ }
  intro F hF i
  exact (value_norm_mono_precision hpq (F i)).trans ((hr.inputBound F hF i).trans (by norm_num))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
