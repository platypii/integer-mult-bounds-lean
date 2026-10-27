module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryLineError

/-! Transfer constructed boundary entry accuracy to the actual integer rank solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open scoped BigOperators
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.BandList

variable {s : ℕ} [NeZero s]

/-- Entry accuracy on boundary coordinates gives row accuracy on natural ranks. -/
theorem boundary_rank_row_error (A q w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) (hA : 4 ≤ A) (hw : 1 ≤ w)
    (R : Matrix (ZMod s) (ZMod s) ℝ) (ε : ℝ)
    (herror : ∀ i ∈ B, ∀ j ∈ B,
      |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j - R i j| ≤ ε) :
    ∀ i ∈ Finset.range B.card, ∑ j ∈ Finset.range B.card,
      |gvM q (factorRankIntegerMatrix B W columns) i j -
        R (bFoldAt s B i) (bFoldAt s B j)| ≤ (B.card : ℝ)*ε := by
  rw [factorRankIntegerMatrix_value A q w B W columns hlen hformat hA hw]
  intro i hi
  calc
    _ ≤ ∑ j ∈ Finset.range B.card, ε := by
      apply Finset.sum_le_sum
      intro j hj
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      simpa only [factorRankMatrix, hi', hj', and_self, ite_true] using
        herror _ (bFoldAt_mem s B i hi') _ (bFoldAt_mem s B j hj')
    _ = _ := by simp

theorem boundary_rank_allocated_error (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (W : ℕ) (columns : List (ZMod s → GaussianInt))
    (hp : 2 ≤ p) (hA : 4 ≤ A) (hlen : columns.length = B.card) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
      (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ (bZ : List ℤ), bZ.length = B.card →
    (∀ i < B.card, |gv q (bZ.getD i 0)| ≤ 1/2) →
    ∀ (R : Matrix (ZMod s) (ZMod s) ℝ) (x b : ℕ → ℝ), Solves (fun i j => R (bFoldAt s B i) (bFoldAt s B j)) (Finset.range B.card) x b →
    ∀ (ε δ X : ℝ), 0 ≤ X →
    (∀ i ∈ B, ∀ j ∈ B,
      |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j - R i j| ≤ ε) →
    (∀ i ∈ Finset.range B.card, |gv q (bZ.getD i 0) - b i| ≤ δ) →
    (∀ i ∈ Finset.range B.card, |x i| ≤ X) →
    ∀ i < B.card, |gv q ((lineSolveZ q K W B.card AZ bZ).getD i 0) - x i| ≤
      62000*(2*(p : ℝ))^3*(B.card : ℝ)^2*
        ((1/2^q : ℝ)*(1+60*3/(1/(32*(p : ℝ)))^2)) +
      (δ + ((B.card : ℝ)*ε)*X)/(1/(8*(2*(p : ℝ)))) := by
  dsimp only
  intro hformat hstage bZ hb hbound R x b hx ε δ X hX herror hrhs hsol i hi
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have hw : 1 ≤ w := by dsimp [w,executionWidth]; omega
  exact boundary_line_allocated_error A p u l target rhsExp B W columns hp hA hlen
    hformat hstage bZ hb hbound (fun i j => R (bFoldAt s B i) (bFoldAt s B j))
    x b hx ((B.card : ℝ)*ε) δ X hX
    (boundary_rank_row_error A q w B W columns hlen hformat hA hw R ε herror)
    hrhs hsol i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
