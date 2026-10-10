import IntegerMultBounds.Machine.CompactSpectatorLeafGuardBudget
import IntegerMultBounds.Parameters
import IntegerMultBounds.Networks.ComplexRecursiveCallSchema
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The actual integer stopping test bounds the literal guarded leaf visit
count by the original global axis dimension to beta. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafCutoffBudget
noncomputable section
open CompactComplexRecursiveGeometry

theorem stopped_count (D k : ℕ) (hD : 0<D)
    (hs : Networks.ComplexRecursiveCallSchema.stopped D k=true) :
    (arity^k : ℝ)≤(D : ℝ)^Parameters.beta := by
  obtain hk | ht := (Networks.ComplexRecursiveCallSchema.stopped_iff D k).mp hs
  · subst k
    simp only [pow_zero]
    exact Real.one_le_rpow (by exact_mod_cast hD) (by norm_num [Parameters.beta])
  · have hp : (arity^k : ℝ)^(1000 : ℕ)≤(D : ℝ) := by
      have hp := (Nat.cast_le (α:=ℝ)).mpr ht.le
      rw [Nat.cast_pow] at hp
      convert hp using 1
      rw [Nat.cast_pow]
      rfl
    have he : Parameters.beta=(1000 : ℝ)⁻¹ := by norm_num [Parameters.beta]
    rw [he,Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num)]
    rw [← Real.rpow_natCast (arity^k : ℝ) 1000] at hp
    exact hp

end
end IntegerMultBounds.Machine.CompactSpectatorLeafCutoffBudget
