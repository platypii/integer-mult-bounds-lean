module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnscaledSolveError
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryTotalErrorBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizedRhsError

/-! Accuracy of the boundary solve on the actual normalized retained residual. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.BandList IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem boundary_unscaled_solve_target (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
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
    ∀ (δ : ℝ), δ ≤ 1/(2 : ℝ)^boundaryErrorBits p target rhsExp →
    (∀ i ∈ B, ∀ j ∈ B,
      |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j - R i j| ≤ 1/(2 : ℝ)^bits) →
    (∀ j ∈ B, |gv q (C j).re| ≤ (2 : ℝ)^couplingRowExponent rhsExp
        (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv q (C j).im| ≤ (2 : ℝ)^couplingRowExponent rhsExp
        (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    (∀ j ∈ B, ‖value q (C j) - b j‖ ≤ δ) →
    (∀ i ∈ B, ‖x i‖ ≤ 16*(p : ℝ)*(2 : ℝ)^rhsExp) →
    ∀ i < B.card, ‖value q (unscaleBoundaryWord q ((bandSolveVec q W (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) rhs).getD i 0)) - x (bFoldAt s B i)‖ ≤
      3/(2 : ℝ)^target := by
  dsimp only
  intro C hformat hstage R x b hxre hxim δ hδ herror hmag hrhs hsol i hi
  let bits := boundaryTableBits p target rhsExp B.card
  let ε : ℝ := 1/(2 : ℝ)^bits
  let X : ℝ := 16*(p : ℝ)*(2 : ℝ)^rhsExp
  have h := boundary_unscaled_solve_error A p u l target rhsExp B W columns hp hA hlen
    C hformat hstage R x b hxre hxim ε δ X (by positivity) herror hmag hrhs hsol i hi
  have hb := boundary_unscaled_total_error_budget p u l target rhsExp B.card (by omega) ε δ X
  have hpert := boundary_perturbation_target p target rhsExp B.card (by omega)
    ((B.card : ℝ)*ε) δ X (by positivity)
    (boundaryTable_error_budget p target rhsExp B.card) hδ (by rfl)
  have he : (2 : ℝ)^(target+1) = (2 : ℝ)^target*2 := by rw [pow_succ]
  have hfinal : 2/(2 : ℝ)^target + 1/(2 : ℝ)^(target+1) ≤ 3/(2 : ℝ)^target := by
    rw [he]
    have heq : 2/(2 : ℝ)^target + 1/((2 : ℝ)^target*2) = (5/2 : ℝ)/(2 : ℝ)^target := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  exact (h.trans hb).trans ((add_le_add le_rfl hpert).trans hfinal)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
