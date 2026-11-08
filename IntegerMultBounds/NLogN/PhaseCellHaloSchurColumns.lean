module

public import IntegerMultBounds.NLogN.PhaseCellPrincipalSchurColumns

/-! Local Schur-column error from approximate original-matrix columns. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open Finset SchurDominance PhaseCellDiscreteGeometry

variable {s t : ℕ} [NeZero s]

theorem halo_schur_column_error (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u a b : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (R : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ c, Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) (R c) c)
    (j : ZMod s) (hj : j ∈ haloBoundary s t (PhaseCellBand.width p u) a b)
    (c r : ZMod s → ℝ) (η E : ℝ) (hη : 0 ≤ η)
    (hcolumn : ∀ k ∈ haloVertices s a b, |c k-realMatrix s t p u k j| ≤ η)
    (hresidual : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |r i-residual (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) R c i| ≤ E) :
    ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      |r i-(run (realMatrix s t p u) (haloVertices s a b)
        (haloInterior s t (PhaseCellBand.width p u) a b).toList).1 i j| ≤ E+(1+16*(p : ℝ))*η := by
  exact principal_schur_column_error hst hα p u hp hwidth hαu hθ hgap hbudget
    (haloVertices s a b) (haloInterior s t (PhaseCellBand.width p u) a b)
    (haloInterior_subset s t _ a b) R hR j hj c r η E hη hcolumn hresidual

end IntegerMultBounds.NLogN.PhaseCellMatrix
