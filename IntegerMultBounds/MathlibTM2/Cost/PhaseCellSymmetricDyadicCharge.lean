module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCanonicalDyadicCharge

/-! Reversing the rectangle exchanges execution order but preserves its charge. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

@[simp] theorem DyadicTransposePlan.weightedCharge_cast_right {a b b' W : ℕ}
    (h : b = b') (plan : DyadicTransposePlan a b W) (f : ℕ → ℝ) :
    (h ▸ plan).weightedCharge f = plan.weightedCharge f := by
  subst b'
  rfl

theorem dyadicTransposePlan_weightedCharge_swap (fuel a b W : ℕ)
    (h : a+b ≤ fuel) (f : ℕ → ℝ) :
    (dyadicTransposePlan fuel a b W h).weightedCharge f =
      (dyadicTransposePlan fuel b a W (by omega)).weightedCharge f := by
  cases fuel with
  | zero =>
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a
    subst b
    rfl
  | succ fuel =>
    by_cases ha : a = 0
    · subst a
      by_cases hb : b = 0 <;> simp [dyadicTransposePlan,hb,DyadicTransposePlan.weightedCharge]
    by_cases hb : b = 0
    · subst b
      simp [dyadicTransposePlan,DyadicTransposePlan.weightedCharge,ha]
    by_cases he : a = b
    · subst b; rfl
    conv_lhs => rw [dyadicTransposePlan]
    conv_rhs => rw [dyadicTransposePlan]
    by_cases hab : a < b
    · simp only [ha,hb,dite_false,dite_true,show ¬b ≤ a by omega,show a ≤ b by omega,
        DyadicTransposePlan.weightedCharge_cast,DyadicTransposePlan.weightedCharge_cast_right,
        DyadicTransposePlan.weightedCharge]
    · simp only [ha,hb,dite_false,dite_true,show b ≤ a by omega,show ¬a ≤ b by omega,
        DyadicTransposePlan.weightedCharge_cast,DyadicTransposePlan.weightedCharge_cast_right,
        DyadicTransposePlan.weightedCharge]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
