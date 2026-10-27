module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolutionError
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizedRhsError

/-! Accuracy of the boundary solve on the actual normalized retained residual. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.BandList IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem boundary_normalized_solution_error (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
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
      (fun i => (x i).re) (fun i => (b i/(2 : ℂ)^(q/2+1)).re) →
    Solves R B
      (fun i => (x i).im) (fun i => (b i/(2 : ℂ)^(q/2+1)).im) →
    ∀ (ε δ X : ℝ), 0 ≤ X →
    (∀ i ∈ B, ∀ j ∈ B,
      |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j - R i j| ≤ ε) →
    (∀ j ∈ B, |gv q (C j).re| ≤ (2 : ℝ)^couplingRowExponent rhsExp
        (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv q (C j).im| ≤ (2 : ℝ)^couplingRowExponent rhsExp
        (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    (∀ j ∈ B, ‖value q (C j) - b j‖ ≤ δ) →
    (∀ i ∈ B, ‖x i‖ ≤ X) →
    ∀ i < B.card, ‖value q ((bandSolveVec q W (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) rhs).getD i 0) - x (bFoldAt s B i)‖ ≤
      2 * (62000*(2*(p : ℝ))^3*(B.card : ℝ)^2*
        ((1/2^q : ℝ)*(1+60*3/(1/(32*(p : ℝ)))^2)) +
      ((2/(2 : ℝ)^q + δ/(2 : ℝ)^(q/2+1)) + ((B.card : ℝ)*ε)*X)/(1/(8*(2*(p : ℝ))))) := by
  dsimp only
  intro C hformat hstage R x b hxre hxim ε δ X hX herror hmag hrhs hsol i hi
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let rhs := ((List.range B.card).map (fun j => C (bFoldAt s B j))).map
    (normalizeBoundaryWord q (q/2-1))
  obtain ⟨hlenR,hbound,herr⟩ := boundary_normalized_rhs_spec p u l target rhsExp B C b δ hmag hrhs
  exact boundary_solution_coordinate_error A p u l target rhsExp B W columns hp hA hlen
    hformat hstage rhs hlenR hbound R x (fun j => b j/(2 : ℂ)^(q/2+1)) hxre hxim
    ε (2/(2 : ℝ)^q + δ/(2 : ℝ)^(q/2+1)) X hX herror
    (fun j hj => herr j (Finset.mem_range.mp hj)) hsol i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
