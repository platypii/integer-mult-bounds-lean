module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySchurAdapters

/-! Actual unscaled boundary solve accuracy from native retained Schur postconditions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.BandList IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem boundary_real_schur_target (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
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
    ∀ i < B.card, ‖value q (unscaleBoundaryWord q ((bandSolveVec q W
      (naturalLineLc q K W B.card AZ) (naturalLineUc q K W B.card AZ)
      (naturalLineRcs q K W B.card AZ) rhs).getD i 0)) - (x (bFoldAt s B i) : ℂ)‖ ≤
      3/(2 : ℝ)^target := by
  dsimp only
  intro C hformat hstage M I hIB hM R hR x b hx hb herror hmag hreal herr i hi
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hschur := boundary_exact_schur_solves M I B hIB _ hμ hM R hR x b hx
  have hre : Solves (run M (I ∪ B) I.toList).1 B
      (fun j => ((x j : ℂ)).re) (fun j => ((residual M I R b j : ℝ) : ℂ).re) := by
    simpa only [Complex.ofReal_re] using hschur
  have him : Solves (run M (I ∪ B) I.toList).1 B
      (fun j => ((x j : ℂ)).im) (fun j => ((residual M I R b j : ℝ) : ℂ).im) := by
    intro j hj
    simp [Complex.ofReal_im]
  have hbound : ∀ j ∈ B, ‖(x j : ℂ)‖ ≤ 16*(p : ℝ)*(2 : ℝ)^rhsExp := by
    intro j hj
    have h := solves_bound M (I ∪ B) _ hμ hM x b hx ((2 : ℝ)^rhsExp) hb j
      (Finset.mem_union_right I hj)
    rw [div_div_eq_mul_div,div_one] at h
    rw [Complex.norm_real,Real.norm_eq_abs]
    nlinarith only [h,show (0 : ℝ) ≤ (p : ℝ)*(2 : ℝ)^rhsExp by positivity]
  exact boundary_unscaled_solve_target A p u l target rhsExp B W columns hp hA hlen
    C hformat hstage (run M (I ∪ B) I.toList).1
    (fun j => (x j : ℂ)) (fun j => (residual M I R b j : ℂ)) hre him
    (1/(2 : ℝ)^boundaryErrorBits p target rhsExp) le_rfl herror hmag
    (fun j hj => boundary_retained_rhs_accuracy q p target rhsExp B.card (by omega)
      (C j) _ (hreal j hj) (herr j hj)) hbound i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
