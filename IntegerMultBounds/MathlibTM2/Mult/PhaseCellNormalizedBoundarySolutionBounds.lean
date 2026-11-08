module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolutionBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizationBudget

/-! Normalize arbitrary bounded boundary rows once and expose the solve format needed for unscaling. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.BandFactor

theorem normalizedBoundarySolution_bounds (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (W : ℕ) (columns : List (ZMod s → GaussianInt))
    (hp : 2 ≤ p) (hA : 4 ≤ A) (hlen : columns.length = B.card) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ xs : List GaussianInt, xs.length = B.card →
    (∀ z ∈ xs, |gv q z.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv q z.im| ≤ (2 : ℝ)^couplingRowExponent rhsExp (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    let solution := bandSolveVec q W (naturalLineLc q K W B.card AZ) (naturalLineUc q K W B.card AZ)
      (naturalLineRcs q K W B.card AZ) (xs.map (normalizeBoundaryWord q (q/2-1)))
    solution.length = B.card ∧ (∀ z ∈ solution, |gv q z.re| ≤ 8*p+1 ∧ |gv q z.im| ≤ 8*p+1) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  intro hformat hstage xs hxs hbound
  obtain ⟨hq,heven,_,_⟩ := boundary_normalization_precision p u l target rhsExp B.card
  change 2 ≤ q at hq
  change q%2 = 0 at heven
  have hsplit : q = q/2+(q/2-1)+1 := by omega
  have hlen' : (xs.map (normalizeBoundaryWord q (q/2-1))).length = B.card := by simp [hxs]
  have hnormalized : ∀ z ∈ xs.map (normalizeBoundaryWord q (q/2-1)),
      |gv q z.re| ≤ 1/2 ∧ |gv q z.im| ≤ 1/2 := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact normalizeBoundaryWord_bound q (q/2) (q/2-1) hsplit x
      (boundary_residual_normalization_bound p u l target rhsExp B.card x (hbound x hx))
  exact ⟨naturalLineSolve_length q _ W B.card _ _ hlen',
    boundary_line_allocated_solution_bounds A p u l target rhsExp B W columns hp hA hlen
      hformat hstage _ hlen' hnormalized⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
