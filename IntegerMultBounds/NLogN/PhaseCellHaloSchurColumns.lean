module

public import IntegerMultBounds.NLogN.SchurColumns
public import IntegerMultBounds.NLogN.PhaseCellHaloSchurStability

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
  let : NeZero t := ⟨by omega⟩
  let I := haloInterior s t (PhaseCellBand.width p u) a b
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  have hU : I∪B = haloVertices s a b := haloInterior_union_boundary s t _ a b
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    positivity
  have hA := dominates_mono (realMatrix s t p u) univ (I∪B) _ (subset_univ _)
    (matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget)
  have hmass (i : ZMod s) (_hi : i ∈ B) : ∑ k ∈ I, |realMatrix s t p u i k| ≤ (2 : ℝ) := by
    calc
      _ ≤ ∑ k, |realMatrix s t p u i k| := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
      _ = ∑ k, realMatrix s t p u i k := by
        apply sum_congr rfl
        intro k _
        apply abs_of_nonneg
        unfold realMatrix
        exact_mod_cast matrix_nonneg s t p u i k
      _ ≤ 2 := matrix_row_sum_le_two hst hα p u hp hwidth hαu hθ hgap hbudget i
  have hh := schur_column_error (realMatrix s t p u) I B
    (haloInterior_disjoint_boundary s t _ a b) _ hμ hA R hR j hj c r η E 2 hη
    (by simpa only [hU] using hcolumn) hresidual hmass
  have herror : E+(η+2*(η/(1/(8*(p : ℝ))))) = E+(1+16*(p : ℝ))*η := by
    field_simp
    ring
  rw [hU] at hh
  simpa only [herror] using hh

end IntegerMultBounds.NLogN.PhaseCellMatrix
