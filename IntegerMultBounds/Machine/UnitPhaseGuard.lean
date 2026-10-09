import IntegerMultBounds.Machine.CompactLiteralUnitPhase
import IntegerMultBounds.Machine.ButterflyGuard

/-! The phase negation guard follows from the existing actual bounded-grid
invariant and fixed fallback signed width. It is not a new machine or codec
correctness premise, and phase application keeps dyadic precision unchanged. -/
namespace IntegerMultBounds.Machine.UnitPhaseGuard
noncomputable section
open ButterflySigned
open Networks.GaussianPrecision

theorem strict (a : ButterflyStreamData.Coefficient) (p D j : ℕ) (hj : j≤D)
    (hgrid : BoundedGrid (p+j) ((2^p)*4^j)
      (complexValue (signedValue (ButterflyGuard.halfWidth p D) a.1)
        (signedValue (ButterflyGuard.halfWidth p D) a.2) (p+j))) :
    ∀ i : Fin 2,|signedValue (ButterflyGuard.halfWidth p D) (UnitPhaseStreamEndpoint.components a i.val)|<
      (2^(ButterflyGuard.halfWidth p D) : ℕ) := by
  have h := ButterflyGuard.represented_bound _ _ (p+j) ((2^p)*4^j) hgrid
  have hn : (2^p)*4^j<2^(ButterflyGuard.halfWidth p D) := by
    have hg := ButterflyGuard.guard p D j hj
    omega
  have hg : (((2^p)*4^j : ℕ) : ℤ)<(2^(ButterflyGuard.halfWidth p D) : ℕ) := by
    exact_mod_cast hn
  intro i
  fin_cases i
  · exact h.1.trans_lt hg
  · exact h.2.trans_lt hg

end
end IntegerMultBounds.Machine.UnitPhaseGuard
