module

public import IntegerMultBounds.NLogN.SchurColumns

/-! Separate matrix and right-hand-side perturbations of an exact solve. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset
variable {ι : Type*} [DecidableEq ι]

/-- Compare exact solves using the computed matrix's dominance margin. -/
theorem solves_perturbation_bound (A Ah : Matrix ι ι ℝ) (S : Finset ι)
    (μ : ℝ) (hμ : 0 < μ) (hAh : DominatesOn Ah S μ)
    (x y b bh : ι → ℝ) (hx : Solves A S x b) (hy : Solves Ah S y bh)
    (ε δ X : ℝ) (hX : 0 ≤ X)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, |Ah i j - A i j| ≤ ε)
    (hrhs : ∀ i ∈ S, |bh i - b i| ≤ δ)
    (hbound : ∀ j ∈ S, |x j| ≤ X) (i : ι) (hi : i ∈ S) :
    |y i - x i| ≤ (δ + ε * X) / μ := by
  let r := fun k => bh k - b k - ∑ j ∈ S, (Ah k j - A k j) * x j
  have hd : Solves Ah S (fun j => y j - x j) r := by
    intro k hk
    dsimp [r]
    simp only [mul_sub, sub_mul, sum_sub_distrib, hy k hk, hx k hk]
    ring
  have hr : ∀ k ∈ S, |r k| ≤ δ + ε * X := by
    intro k hk
    have he := row_bound (fun k j => Ah k j - A k j) S x k ε X
      (hrow k hk) hX hbound
    exact (abs_sub _ _).trans (add_le_add (hrhs k hk) he)
  exact solves_bound Ah S μ hμ hAh _ r hd _ hr i hi

end IntegerMultBounds.NLogN.SchurDominance
