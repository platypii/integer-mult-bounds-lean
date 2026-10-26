module

public import IntegerMultBounds.NLogN.SchurBlockSolve

/-! Recovery is stable under an error in its computed right-hand side. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset

variable {ι : Type*} [DecidableEq ι]

theorem recovery_solves_error (A : Matrix ι ι ℝ) (I B : Finset ι) (hIB : Disjoint I B)
    (μ : ℝ) (hμ : 0 < μ) (hA : DominatesOn A (I∪B) μ)
    (x b y c : ι → ℝ) (hx : Solves A (I∪B) x b) (hy : Solves A I y c)
    (E : ℝ) (hc : ∀ i ∈ I, |c i-(b i-couple A B x i)| ≤ E) :
    ∀ i ∈ I, |y i-x i| ≤ E/μ := by
  have hxI : Solves A I x (fun i => b i-couple A B x i) := by
    intro i hi
    have hh := hx i (mem_union_left B hi)
    rw [sum_union hIB] at hh
    dsimp only [couple]
    linarith
  have hdiff : Solves A I (y-x) (fun i => c i-(b i-couple A B x i)) := by
    intro i hi
    simp only [Pi.sub_apply,mul_sub,sum_sub_distrib,hy i hi,hxI i hi]
  exact solves_bound A I μ hμ (dominates_mono A (I∪B) I μ subset_union_left hA)
    (y-x) _ hdiff E hc

end IntegerMultBounds.NLogN.SchurDominance
