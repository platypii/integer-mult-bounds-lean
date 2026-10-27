module

public import IntegerMultBounds.NLogN.SchurBoundaryResidual

/-! Compute Schur entries by interior responses to approximate original-matrix columns. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset

variable {ι : Type*} [DecidableEq ι]

/-- An original-matrix column's residual is the corresponding Schur column. -/
theorem residual_column_eq_run (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B)
    (μ : ℝ) (hμ : 0 < μ) (hA : DominatesOn A (I∪B) μ)
    (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c)
    (i j : ι) (hi : i ∈ B) (hj : j ∈ B) :
    residual A I R (fun k => A k j) i = (run A (I∪B) I.toList).1 i j := by
  let e := fun k => if k = j then (1 : ℝ) else 0
  have hc : couple A B e = fun k => A k j := by
    funext k
    simp [couple,e,hj]
  have hh := schurOp_eq_run A I B hIB μ hμ hA R hR I.toList (toList_toFinset I) e i hi
  simpa [schurOp,residual,hc,e,hj] using hh

theorem solver_lipschitz (A : Matrix ι ι ℝ) (I : Finset ι) (μ : ℝ) (hμ : 0 < μ)
    (hA : DominatesOn A I μ) (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c)
    (c c' : ι → ℝ) (η : ℝ) (hη : ∀ k ∈ I, |c k-c' k| ≤ η) :
    ∀ k ∈ I, |R c k-R c' k| ≤ η/μ := by
  intro k hk
  rw [← solver_sub A I μ hμ hA R hR c c' k hk]
  exact solves_bound A I μ hμ hA _ _ (hR (c-c')) η hη k hk

/-- Input-column error is amplified only by the interior inverse and the stated row mass. -/
theorem residual_lipschitz (A : Matrix ι ι ℝ) (I : Finset ι) (μ : ℝ) (hμ : 0 < μ)
    (hA : DominatesOn A I μ) (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c)
    (c c' : ι → ℝ) (η K : ℝ) (hη : 0 ≤ η)
    (hinput : ∀ k ∈ I, |c k-c' k| ≤ η) (i : ι) (hi : |c i-c' i| ≤ η)
    (hmass : ∑ k ∈ I, |A i k| ≤ K) :
    |residual A I R c i-residual A I R c' i| ≤ η+K*(η/μ) := by
  have hRdiff := solver_lipschitz A I μ hμ hA R hR c c' η hinput
  have hrow := row_bound A I (fun k => R c k-R c' k) i K (η/μ) hmass (by positivity) hRdiff
  have hid : residual A I R c i-residual A I R c' i =
      (c i-c' i)-(∑ k ∈ I, A i k*(R c k-R c' k)) := by
    simp only [residual,mul_sub,sum_sub_distrib]
    ring
  rw [hid,sub_eq_add_neg]
  calc
    _ ≤ |c i-c' i|+|∑ k ∈ I, A i k*(R c k-R c' k)| := by
      simpa only [abs_neg] using abs_add_le (c i-c' i) (-(∑ k ∈ I, A i k*(R c k-R c' k)))
    _ ≤ _ := add_le_add hi hrow

/-- An approximate original column and its computed residual give a computed
Schur column, charging coefficient and interior/coupling errors separately. -/
theorem schur_column_error (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B)
    (μ : ℝ) (hμ : 0 < μ) (hA : DominatesOn A (I∪B) μ)
    (R : (ι → ℝ) → ι → ℝ) (hR : ∀ c, Solves A I (R c) c)
    (j : ι) (hj : j ∈ B) (c r : ι → ℝ) (η E K : ℝ) (hη : 0 ≤ η)
    (hcolumn : ∀ k ∈ I∪B, |c k-A k j| ≤ η)
    (hresidual : ∀ i ∈ B, |r i-residual A I R c i| ≤ E)
    (hmass : ∀ i ∈ B, ∑ k ∈ I, |A i k| ≤ K) :
    ∀ i ∈ B, |r i-(run A (I∪B) I.toList).1 i j| ≤ E+(η+K*(η/μ)) := by
  have hAI := dominates_mono A (I∪B) I μ subset_union_left hA
  intro i hi
  rw [← residual_column_eq_run A I B hIB μ hμ hA R hR i j hi hj]
  calc
    _ ≤ |r i-residual A I R c i|+
        |residual A I R c i-residual A I R (fun k => A k j) i| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (hresidual i hi)
      (residual_lipschitz A I μ hμ hAI R hR c (fun k => A k j) η K hη
        (fun k hk => hcolumn k (mem_union_left _ hk)) i (hcolumn i (mem_union_right _ hi)) (hmass i hi))

end IntegerMultBounds.NLogN.SchurDominance
