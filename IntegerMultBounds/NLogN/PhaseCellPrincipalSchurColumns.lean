module

public import IntegerMultBounds.NLogN.SchurColumns
public import IntegerMultBounds.NLogN.PhaseCellHaloSchurStability

/-! Column accuracy for arbitrary principal shapes of the original phase-cell matrix. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix
open scoped BigOperators
open Finset SchurDominance
variable {s t : ℕ} [NeZero s]

theorem principal_schur_column_error (hst : s < t) {alpha gap : ℝ} (halpha : 0 < alpha)
    (p u : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hsquare : alpha^2 = (u : ℝ))
    (htheta : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1)) (hbudget : alpha^2*gap ≤ p)
    (vertices interior : Finset (ZMod s)) (hsub : interior ⊆ vertices)
    (R : (ZMod s → ℝ) → ZMod s → ℝ)
    (hR : ∀ rhs, Solves (realMatrix s t p u) interior (R rhs) rhs)
    (j : ZMod s) (hj : j ∈ vertices\interior)
    (c r : ZMod s → ℝ) (eta E : ℝ) (heta : 0 ≤ eta)
    (hcolumn : ∀ k ∈ vertices, |c k-realMatrix s t p u k j| ≤ eta)
    (hresidual : ∀ i ∈ vertices\interior, |r i-residual (realMatrix s t p u) interior R c i| ≤ E) :
    ∀ i ∈ vertices\interior,
      |r i-(run (realMatrix s t p u) vertices interior.toList).1 i j| ≤ E+(1+16*(p : ℝ))*eta := by
  let : NeZero t := ⟨by omega⟩
  let boundary := vertices\interior
  have hU : interior∪boundary = vertices := by
    ext k
    simp only [boundary,mem_union,mem_sdiff]
    constructor
    · rintro (hi | ⟨hv,_⟩)
      · exact hsub hi
      · exact hv
    · intro hv
      by_cases hi : k ∈ interior
      · exact Or.inl hi
      · exact Or.inr ⟨hv,hi⟩
  have hdisj : Disjoint interior boundary := disjoint_left.mpr (fun _ hi hb => (mem_sdiff.mp hb).2 hi)
  have hmu : (0 : ℝ) < 1/(8*(p : ℝ)) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    positivity
  have hdom := dominates_mono (realMatrix s t p u) univ (interior∪boundary) _ (subset_univ _)
    (matrix_gap s t hst halpha p u hp hwidth hsquare htheta hgap hbudget)
  have hmass (i : ZMod s) (_hi : i ∈ boundary) : ∑ k ∈ interior, |realMatrix s t p u i k| ≤ (2 : ℝ) := by
    calc
      _ ≤ ∑ k, |realMatrix s t p u i k| := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
      _ = ∑ k, realMatrix s t p u i k := by
        apply sum_congr rfl
        intro k _
        apply abs_of_nonneg
        unfold realMatrix
        exact_mod_cast matrix_nonneg s t p u i k
      _ ≤ 2 := matrix_row_sum_le_two hst halpha p u hp hwidth hsquare htheta hgap hbudget i
  have hh := schur_column_error (realMatrix s t p u) interior boundary hdisj _ hmu hdom R hR
    j hj c r eta E 2 heta (by simpa only [hU] using hcolumn) hresidual hmass
  have he : E+(eta+2*(eta/(1/(8*(p : ℝ))))) = E+(1+16*(p : ℝ))*eta := by
    field_simp
    ring
  rw [hU] at hh
  simpa only [he] using hh

end IntegerMultBounds.NLogN.PhaseCellMatrix
