module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRealSchurTarget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolutionBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryExactBounds

/-! Actual unscaled boundary solve accuracy from native retained Schur postconditions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.BandList IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem boundary_residual_solution_accuracy (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
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
    ∀ (M : Matrix (ZMod s) (ZMod s) ℝ) (I : Finset (ZMod s)), Disjoint I B →
    DominatesOn M (I ∪ B) (1/(8*(p : ℝ))) →
    ∀ (R : (ZMod s → ℝ) → ZMod s → ℝ), (∀ c, Solves M I (R c) c) →
    ∀ (x b : ZMod s → ℝ), Solves M (I ∪ B) x b →
    (∀ j ∈ I ∪ B, |b j| ≤ (2 : ℝ)^rhsExp) →
    (∀ i ∈ B, ∀ j ∈ B,
      |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j -
        (run M (I ∪ B) I.toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    (∀ j ∈ B, |gv q (C j).re| ≤ (2 : ℝ)^couplingRowExponent rhsExp
        (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv q (C j).im| ≤ (2 : ℝ)^couplingRowExponent rhsExp
        (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    (∀ j ∈ B, (C j).im = 0) →
    (∀ j ∈ B, 8*(p : ℝ)*|(value q (C j)).re-residual M I R b j| ≤
      1/(2 : ℝ)^(recoveryTarget p bits+2)) →
    let normalizedSolution := bandSolveVec q W
      (naturalLineLc q K W B.card AZ) (naturalLineUc q K W B.card AZ)
      (naturalLineRcs q K W B.card AZ) rhs
    let solution := normalizedSolution.map (unscaleBoundaryWord q)
    solution.length = B.card ∧ ∀ i < B.card,
      ‖value q (solution.getD i 0) - (x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
      ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  intro C hformat hstage M I hIB hM R hR x b hx hb herror hmag hreal herr
  let rhs := ((List.range B.card).map (fun j => C (bFoldAt s B j))).map
    (normalizeBoundaryWord q (q/2-1))
  let sol := bandSolveVec q W (naturalLineLc q K W B.card AZ)
    (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) rhs
  have hlenSol : sol.length = B.card := naturalLineSolve_length q K W B.card AZ rhs (by simp [rhs])
  refine ⟨by simpa only [List.length_map] using hlenSol,?_⟩
  intro i hi
  have hiSol : i < sol.length := by rw [hlenSol]; exact hi
  have hget : (sol.map (unscaleBoundaryWord q)).getD i 0 = unscaleBoundaryWord q (sol.getD i 0) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hiSol),
      List.getD_eq_getElem _ _ hiSol,List.getElem_map]
  change ‖value q ((sol.map (unscaleBoundaryWord q)).getD i 0) - (x (bFoldAt s B i) : ℂ)‖ ≤ _ ∧ _
  rw [hget]
  have hacc := boundary_real_schur_target A p u l target rhsExp B W columns hp hA hlen
    C hformat hstage M I hIB hM R hR x b hx hb herror hmag hreal herr i hi
  have hxBound : ‖(x (bFoldAt s B i) : ℂ)‖ ≤ 16*(p : ℝ)*(2 : ℝ)^rhsExp := by
    have h := solves_bound M (I ∪ B) _ (by positivity) hM x b hx
      ((2 : ℝ)^rhsExp) hb _ (Finset.mem_union_right I (bFoldAt_mem s B i hi))
    rw [div_div_eq_mul_div,div_one] at h
    rw [Complex.norm_real,Real.norm_eq_abs]
    nlinarith only [h,show (0 : ℝ) ≤ (p : ℝ)*(2 : ℝ)^rhsExp by positivity]
  exact ⟨hacc,boundary_computed_solution_magnitude p rhsExp target (by omega) _ _ hxBound hacc⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
