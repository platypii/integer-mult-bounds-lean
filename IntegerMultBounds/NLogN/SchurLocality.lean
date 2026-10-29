module

public import IntegerMultBounds.NLogN.SchurSolve

/-! # Local decay in a diagonally dominant system

A homogeneous row contracts a uniform bound on its neighbors. Iterating over
nested neighborhoods gives exponential decay into a halo, without summing over
its volume. Neighborhoods are abstract: geometry supplies only support inclusion.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset
variable {ι : Type*} [DecidableEq ι]

/-- A diagonal bounded by two turns an additive dominance margin into a
uniform multiplicative contraction. -/
theorem dominance_row_contraction (A : Matrix ι ι ℝ) (S : Finset ι)
    (μ : ℝ) (hμ : 0 ≤ μ) (hA : DominatesOn A S μ)
    (i : ι) (hi : i ∈ S) (hdiag : A i i ≤ 2) :
    ∑ j ∈ S.erase i, |A i j| ≤ (1 - μ/2) * A i i := by
  have h := hA i hi
  have hm := mul_le_mul_of_nonneg_left hdiag hμ
  nlinarith

/-- A homogeneous row contracts the bound on its nonzero off-diagonal entries. -/
theorem homogeneous_row_bound (A : Matrix ι ι ℝ) (S : Finset ι)
    (z : ι → ℝ) (i : ι) (hi : i ∈ S) (q B : ℝ)
    (hdiag : 0 < A i i) (hB : 0 ≤ B)
    (hrow : ∑ j ∈ S.erase i, |A i j| ≤ q * A i i)
    (hz : ∑ j ∈ S, A i j * z j = 0)
    (hbound : ∀ j ∈ S.erase i, A i j ≠ 0 → |z j| ≤ B) :
    |z i| ≤ q * B := by
  have hsplit := sum_erase_add S (fun j => A i j * z j) hi
  have hoff : |∑ j ∈ S.erase i, A i j * z j| ≤
      (∑ j ∈ S.erase i, |A i j|) * B := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [sum_mul]
    apply sum_le_sum
    intro j hj
    by_cases hzero : A i j = 0
    · simp [hzero]
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbound j hj hzero) (abs_nonneg _)
  have heq : A i i * z i = -(∑ j ∈ S.erase i, A i j * z j) := by
    linarith
  have habs : A i i * |z i| = |∑ j ∈ S.erase i, A i j * z j| := by
    calc
      _ = |A i i * z i| := by rw [abs_mul, abs_of_pos hdiag]
      _ = _ := by rw [heq, abs_neg]
  have hmass := mul_le_mul_of_nonneg_right hrow hB
  nlinarith

/-- Each layer contains every neighbor needed by the next layer. Homogeneous
rows therefore attenuate boundary discrepancies by one factor per layer. -/
theorem homogeneous_layers_bound (A : Matrix ι ι ℝ) (S : Finset ι)
    (layers : ℕ → Finset ι) (z : ι → ℝ) (q B : ℝ)
    (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hbase : ∀ i ∈ layers 0, |z i| ≤ B)
    (hactive : ∀ n i, i ∈ layers (n+1) → i ∈ S)
    (hdiag : ∀ n i, i ∈ layers (n+1) → 0 < A i i)
    (hrow : ∀ n i, i ∈ layers (n+1) →
      ∑ j ∈ S.erase i, |A i j| ≤ q * A i i)
    (hzero : ∀ n i, i ∈ layers (n+1) → ∑ j ∈ S, A i j * z j = 0)
    (hsupport : ∀ n i, i ∈ layers (n+1) →
      ∀ j ∈ S.erase i, A i j ≠ 0 → j ∈ layers n) :
    ∀ n i, i ∈ layers n → |z i| ≤ q^n * B := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    intro i hi
    have h := homogeneous_row_bound A S z i (hactive n i hi) q (q^n * B)
      (hdiag n i hi) (mul_nonneg (pow_nonneg hq _) hB) (hrow n i hi)
      (hzero n i hi) (fun j hj hne => ih j (hsupport n i hi j hj hne))
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h

omit [DecidableEq ι] in
/-- A global solution satisfies a principal row whenever that row has no
nonzero coefficient outside the principal set. -/
theorem Solves.restrict_row (A : Matrix ι ι ℝ) (S T : Finset ι)
    (hST : S ⊆ T) (x b : ι → ℝ) (hx : Solves A T x b)
    (i : ι) (hi : i ∈ S)
    (hsupport : ∀ j ∈ T, j ∉ S → A i j = 0) :
    ∑ j ∈ S, A i j * x j = b i := by
  rw [← hx i (hST hi)]
  exact sum_subset hST (fun j hj hnot => by rw [hsupport j hj hnot, zero_mul])

/-- Exact halo and ambient solutions differ exponentially little on nested
interior layers. Both the initial discrepancy and contraction are derived from
matrix bounds; no error hypothesis about the solutions is supplied. -/
theorem solves_locality (A : Matrix ι ι ℝ) (S T : Finset ι) (hST : S ⊆ T)
    (layers : ℕ → Finset ι) (μ B : ℝ) (hμ : 0 < μ) (hμtwo : μ ≤ 2)
    (hB : 0 ≤ B) (hS : DominatesOn A S μ) (hT : DominatesOn A T μ)
    (hdiag : ∀ i ∈ S, A i i ≤ 2)
    (x y b : ι → ℝ) (hx : Solves A T x b) (hy : Solves A S y b)
    (hb : ∀ i ∈ T, |b i| ≤ B)
    (hlayers : ∀ n, layers n ⊆ S)
    (hexterior : ∀ n i, i ∈ layers (n+1) → ∀ j ∈ T, j ∉ S → A i j = 0)
    (hsupport : ∀ n i, i ∈ layers (n+1) →
      ∀ j ∈ S.erase i, A i j ≠ 0 → j ∈ layers n) :
    ∀ n i, i ∈ layers n → |y i - x i| ≤ (1-μ/2)^n * (2*B/μ) := by
  apply homogeneous_layers_bound A S layers (fun i => y i-x i) (1-μ/2) (2*B/μ)
  · linarith
  · positivity
  · intro i hi
    have hiS := hlayers 0 hi
    have hyB := solves_bound A S μ hμ hS y b hy B
      (fun j hj => hb j (hST hj)) i hiS
    have hxB := solves_bound A T μ hμ hT x b hx B hb i (hST hiS)
    have ht := abs_sub (y i) (x i)
    calc
      |y i-x i| ≤ B/μ+B/μ := ht.trans (add_le_add hyB hxB)
      _ = 2*B/μ := by ring
  · intro n i hi
    exact hlayers (n+1) hi
  · intro n i hi
    exact pivot_pos A S μ hμ hS i (hlayers (n+1) hi)
  · intro n i hi
    exact dominance_row_contraction A S μ hμ.le hS i (hlayers (n+1) hi)
      (hdiag i (hlayers (n+1) hi))
  · intro n i hi
    rw [show (∑ j ∈ S, A i j * (y j-x j)) =
      (∑ j ∈ S, A i j*y j)-(∑ j ∈ S, A i j*x j) by
        simp only [mul_sub, sum_sub_distrib]]
    rw [hy i (hlayers (n+1) hi),
      Solves.restrict_row A S T hST x b hx i (hlayers (n+1) hi) (hexterior n i hi), sub_self]
  · exact hsupport

end IntegerMultBounds.NLogN.SchurDominance
