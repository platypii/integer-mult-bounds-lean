module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizedSolutionError
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizedRhsError

/-! Accuracy of the boundary solve on the actual normalized retained residual. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.BandList IntegerMultBounds.MathlibTM2.Mult.ShortConv

open scoped BigOperators

/-- Scaling the RHS scales its exact solution by the same real divisor. -/
theorem boundary_solves_div {s : ℕ} [NeZero s] (R : Matrix (ZMod s) (ZMod s) ℝ)
    (B : Finset (ZMod s)) (x b : ZMod s → ℝ) (hx : Solves R B x b) (c : ℝ) :
    Solves R B (fun j => x j/c) (fun j => b j/c) := by
  intro i hi
  simp only [← mul_div_assoc, ← Finset.sum_div, hx i hi]

theorem boundary_unscaled_solve_error (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (W : ℕ) (columns : List (ZMod s → GaussianInt))
    (hp : 2 ≤ p) (hA : 4 ≤ A) (hlen : columns.length = B.card) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    ∀ (C : ZMod s → GaussianInt),
    let rhs := ((List.range B.card).map (fun j => C (bFoldAt s B j))).map
      (normalizeBoundaryWord q (q/2-1))
    ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
      (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ (R : Matrix (ZMod s) (ZMod s) ℝ) (x b : ZMod s → ℂ),
    Solves R B
      (fun i => (x i).re) (fun i => (b i).re) →
    Solves R B
      (fun i => (x i).im) (fun i => (b i).im) →
    ∀ (ε δ X : ℝ), 0 ≤ X →
    (∀ i ∈ B, ∀ j ∈ B,
      |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j - R i j| ≤ ε) →
    (∀ j ∈ B, |gv q (C j).re| ≤ (2 : ℝ)^couplingRowExponent rhsExp
        (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv q (C j).im| ≤ (2 : ℝ)^couplingRowExponent rhsExp
        (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    (∀ j ∈ B, ‖value q (C j) - b j‖ ≤ δ) →
    (∀ i ∈ B, ‖x i‖ ≤ X) →
    ∀ i < B.card, ‖value q (unscaleBoundaryWord q ((bandSolveVec q W (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) rhs).getD i 0)) - x (bFoldAt s B i)‖ ≤
      (2 : ℝ)^(q/2+1) * (2 * (62000*(2*(p : ℝ))^3*(B.card : ℝ)^2*
        ((1/2^q : ℝ)*(1+60*3/(1/(32*(p : ℝ)))^2)) +
      ((2/(2 : ℝ)^q + δ/(2 : ℝ)^(q/2+1)) + ((B.card : ℝ)*ε)*(X/(2 : ℝ)^(q/2+1)))/(1/(8*(2*(p : ℝ)))))) := by
  dsimp only
  intro C hformat hstage R x b hxre hxim ε δ X hX herror hmag hrhs hsol i hi
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  have hre : Solves R B (fun j => (x j/(2 : ℂ)^(q/2+1)).re)
      (fun j => (b j/(2 : ℂ)^(q/2+1)).re) := by
    simpa only [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, Complex.div_ofReal_re] using
      boundary_solves_div R B _ _ hxre ((2 : ℝ)^(q/2+1))
  have him : Solves R B (fun j => (x j/(2 : ℂ)^(q/2+1)).im)
      (fun j => (b j/(2 : ℂ)^(q/2+1)).im) := by
    simpa only [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, Complex.div_ofReal_im] using
      boundary_solves_div R B _ _ hxim ((2 : ℝ)^(q/2+1))
  have hbound : ∀ j ∈ B, ‖x j/(2 : ℂ)^(q/2+1)‖ ≤ X/(2 : ℝ)^(q/2+1) := by
    intro j hj
    rw [norm_div,norm_pow]
    norm_num only [Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right (hsol j hj) (by positivity)
  have h := boundary_normalized_solution_error A p u l target rhsExp B W columns hp hA hlen
    C hformat hstage R (fun j => x j/(2 : ℂ)^(q/2+1)) b hre him
    ε δ (X/(2 : ℝ)^(q/2+1)) (by positivity) herror hmag hrhs hbound i hi
  exact boundary_unscaled_solution_error q _ _ _ h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
