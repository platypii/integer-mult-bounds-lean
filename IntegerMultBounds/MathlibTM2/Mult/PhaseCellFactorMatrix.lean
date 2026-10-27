module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRowValues
public import IntegerMultBounds.NLogN.SchurPerturbSolve

/-! Band support and row-error stability of the actual matrix emitted to the factorizer. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open scoped BigOperators
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.SchurDominance

variable {s : ℕ} [NeZero s]

theorem factorRankMatrix_band (A q w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) : BandFrom W (factorRankMatrix A q w B W columns) 0 := by
  intro m n _ _ hne
  by_cases hinside : m < B.card ∧ n < B.card
  · have hrel : FoldBRel s B W (bFoldAt s B m) (bFoldAt s B n) := by
      by_contra hrel
      exact hne (by simp [factorRankMatrix,hinside,bandBoundaryTable,hrel])
    simpa only [FoldBRel,bFoldPos_bFoldAt s B m hinside.1,bFoldPos_bFoldAt s B n hinside.2] using hrel
  · exact False.elim (hne (by simp [factorRankMatrix,hinside]))

omit [NeZero s] in
theorem boundaryTable_row_error (B : Finset (ZMod s)) (W : ℕ)
    (M R : Matrix (ZMod s) (ZMod s) ℝ) (ε : ℝ)
    (herror : ∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W M i j-R i j| ≤ ε) :
    ∀ i ∈ B, ∑ j ∈ B, |bandBoundaryTable B W M i j-R i j| ≤ (B.card : ℝ)*ε := by
  intro i hi
  calc
    _ ≤ ∑ j ∈ B, ε := Finset.sum_le_sum (fun j hj => herror i hi j hj)
    _ = (B.card : ℝ)*ε := by simp

omit [NeZero s] in
theorem boundaryTable_stageInv (B : Finset (ZMod s)) (W : ℕ)
    (M R : Matrix (ZMod s) (ZMod s) ℝ) (μ mass ε : ℝ)
    (hR : StageInv R B μ mass)
    (herror : ∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W M i j-R i j| ≤ ε) :
    StageInv (bandBoundaryTable B W M) B (μ-(B.card : ℝ)*ε) (mass+(B.card : ℝ)*ε) := by
  exact stageInv_perturb R (bandBoundaryTable B W M) B μ mass _ hR
    (boundaryTable_row_error B W M R ε herror)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
