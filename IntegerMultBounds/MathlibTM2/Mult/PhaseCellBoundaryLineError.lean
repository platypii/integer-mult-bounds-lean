module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalLineError
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryLinePrecision
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorAllocatedFits

/-! Allocated forward error for the actually constructed boundary rank matrix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.Sizes
  IntegerMultBounds.MathlibTM2.Mult.BandList

theorem boundary_line_allocated_error (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
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
    ∀ (M : Matrix ℕ ℕ ℝ) (x b : ℕ → ℝ), Solves M (Finset.range B.card) x b →
    ∀ (ε δ X : ℝ), 0 ≤ X →
    (∀ i ∈ Finset.range B.card, ∑ j ∈ Finset.range B.card,
      |gvM q AZ i j - M i j| ≤ ε) →
    (∀ i ∈ Finset.range B.card, |gv q (bZ.getD i 0) - b i| ≤ δ) →
    (∀ i ∈ Finset.range B.card, |x i| ≤ X) →
    ∀ i < B.card, |gv q ((lineSolveZ q K W B.card AZ bZ).getD i 0) - x i| ≤
      62000*(2*(p : ℝ))^3*(B.card : ℝ)^2*
        ((1/2^q : ℝ)*(1+60*3/(1/(32*(p : ℝ)))^2)) +
      (δ + ε*X)/(1/(8*(2*(p : ℝ)))) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro hformat hstage bZ hb hbound M x b hx ε δ X hX hrow hrhs hsol i hi
  have hbits : 5*p+2*Nat.size B.card+40 ≤ q := boundary_line_execution_bits p u l target rhsExp B.card
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hwpos : 1 ≤ w := by omega
  have hinv := boundaryFactor_stageInv_allocated _ p target rhsExp B.card hp hstage
  have hInv : StageInv (gvM q (factorRankIntegerMatrix B W columns)) (Finset.range B.card)
      (1/(8*(2*(p : ℝ)))) (9/4) := by
    rw [factorRankIntegerMatrix_value A q w B W columns hlen hformat hA hwpos]
    exact hinv
  apply naturalLineSolve_perturbed_error q (factorNewtonSteps p q) W B.card (by omega)
    (factorRankIntegerMatrix B W columns)
    (factorRankIntegerMatrix_band A q w B W columns hlen hformat hA hwpos)
    (factorRankIntegerMatrix_out B W columns) p hp hInv (1/(32*(p : ℝ))) (by positivity)
  · apply le_of_eq
    field_simp
    ring
  · exact factor_roundoff_budget p q (by omega) (by omega)
  · exact factorNewtonSteps_budget p q (by omega)
  · exact factor_stage_roundoff_budget p q B.card (by omega) (by omega)
  · exact hb
  · exact hbound
  · exact hx
  · exact hX
  · exact hrow
  · exact hrhs
  · exact hsol
  · exact hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
