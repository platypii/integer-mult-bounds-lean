module

public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalFold
public import IntegerMultBounds.NLogN.PhaseCellPrincipalSchurColumns

/-! Stability and column accuracy for the joint cyclic principal boundary. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open scoped BigOperators
open Finset PhaseCellMatrix SchurDominance
variable {s t : ℕ} [NeZero s]

theorem cyclicPrincipal_schur_stageInv (p u a n : ℕ) (mu mass : ℝ) (hmu : 0 < mu)
    (hdom : DominatesOn (realMatrix s t p u) univ mu)
    (hmass : ∀ i, ∑ j, |realMatrix s t p u i j| ≤ mass) :
    StageInv (run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
      (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1
      (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) mu mass := by
  refine ⟨cyclicPrincipal_schur_gap t p u a n mu hmu hdom,?_⟩
  intro i _
  have hd := dominates_mono (realMatrix s t p u) univ (cyclicPrincipalVertices s a n) mu (subset_univ _) hdom
  have hh := run_mass (realMatrix s t p u) (cyclicPrincipalVertices s a n) mu hmu hd
    (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList i
  rw [run_set,toList_toFinset] at hh
  exact hh.trans ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)).trans (hmass i))

theorem cyclicPrincipal_schur_column_error (hst : s < t) {alpha gap : ℝ} (halpha : 0 < alpha)
    (p u a n : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hsquare : alpha^2 = (u : ℝ))
    (htheta : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1)) (hbudget : alpha^2*gap ≤ p)
    (R : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ rhs, Solves (realMatrix s t p u) (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n) (R rhs) rhs)
    (j : ZMod s) (hj : j ∈ cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n)
    (c r : ZMod s → ℝ) (eta E : ℝ) (heta : 0 ≤ eta)
    (hcolumn : ∀ k ∈ cyclicPrincipalVertices s a n, |c k-realMatrix s t p u k j| ≤ eta)
    (hresidual : ∀ i ∈ cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n,
      |r i-residual (realMatrix s t p u) (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n) R c i| ≤ E) :
    ∀ i ∈ cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n,
      |r i-(run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
        (cyclicPrincipalInterior s t (PhaseCellBand.width p u) a n).toList).1 i j| ≤ E+(1+16*(p : ℝ))*eta :=
  principal_schur_column_error hst halpha p u hp hwidth hsquare htheta hgap hbudget _ _
    (cyclicPrincipalInterior_subset t _ a n) R hR j hj c r eta E heta hcolumn hresidual

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
