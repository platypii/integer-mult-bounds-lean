module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualSolve

/-! Original-scale residual solutions have the row count and word format needed for recovery. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance

theorem boundary_residual_solution_format (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (W : ℕ) (columns : List (ZMod s → GaussianInt))
    (hp : 2 ≤ p) (hA : 4 ≤ A) (hlen : columns.length = B.card) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
      (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ (b : List GaussianInt), b.length = B.card →
    (∀ x ∈ b, |gv q x.re| ≤ (2 : ℝ)^couplingRowExponent rhsExp
      (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv q x.im| ≤ (2 : ℝ)^couplingRowExponent rhsExp
      (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    let solution := (bandSolveVec q W Lc Uc rcs
      (b.map (normalizeBoundaryWord q (q/2-1)))).map (unscaleBoundaryWord q)
    solution.length = B.card ∧ ∀ z ∈ solution, Fits w z := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  intro hformat hstage b hb hbound
  let bs := b.map (normalizeBoundaryWord q (q/2-1))
  let ys := bandSolveVec q W (naturalLineLc q K W B.card AZ)
    (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) bs
  have hys : ys.length = B.card := naturalLineSolve_length q K W B.card AZ bs (by simp [bs,hb])
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hbits : 4*p+2*Nat.size B.card+36 ≤ q := factor_execution_bits p u l target rhsExp B.card
  have hpq : p ≤ q/2 := by omega
  have hbs : ∀ z ∈ bs, |gv q z.re| ≤ 1/2 ∧ |gv q z.im| ≤ 1/2 := by
    obtain ⟨hq,heven,_,_⟩ := boundary_normalization_precision p u l target rhsExp B.card
    change 2 ≤ q at hq
    change q%2 = 0 at heven
    intro z hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact normalizeBoundaryWord_bound q (q/2) (q/2-1) (by omega) x
      (boundary_residual_normalization_bound p u l target rhsExp B.card x (hbound x hx))
  have hsol := boundary_line_allocated_solution_bounds A p u l target rhsExp B W columns
    hp hA hlen hformat hstage bs (by simp [bs,hb]) hbs
  refine ⟨by simpa only [List.length_map] using hys,?_⟩
  intro z hz
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
  change Fits w (unscaleBoundaryWord q x)
  rw [hw]
  exact (boundary_unscale_fits q p hpq x (hsol x hx)).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
