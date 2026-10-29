module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloResidualAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryResidualErrorBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualBoundaryFormat
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySchurAdapters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryExactBounds

/-! Accuracy and recovery format for the boundary solution of the actual halo
residual. Exact interior inversion is chosen from dominance, not supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance

theorem haloBoundary_solution_accuracy (A p u l target rhsExp a b W : ℕ)
    {s t : ℕ} [NeZero s] {α d : ℝ} (columns : List (ZMod s → GaussianInt))
    (hA : 4 ≤ A) (hp : 2 ≤ p) (hst : s < t) (hα : 0 < α) (hwidth : 8*p ≤ 2^u)
    (hαu : α^2 = (u : ℝ)) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hdom : DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ)))) :
    let band := PhaseCellBand.width p u
    let I := haloInterior s t band a b
    let B := haloBoundary s t band a b
    let cellTarget := boundaryHaloTarget p u target rhsExp B.card
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    columns.length = B.card → ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits)) (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
      (run (realMatrix s t p u) (haloVertices s a b) I.toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    ∀ (C D : ZMod s → GaussianInt) (x₀ x : ZMod s → ℝ),
    (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp) →
    Solves (realMatrix s t p u) I x₀ (fun i => (value q (C i)).re) →
    PhaseCellInterface.ErrorOn I (fun i => (value q (D i)).re) x₀ (1/(2 : ℝ)^cellTarget) →
    Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (C i)).re) →
    let rows := (bFoldOrder s B).map (fun i => realPartWord
      (couplingRowField (2^15*p) q t u band a b false D C i))
    let normalized := bandSolveVec q W (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
      (rows.map (normalizeBoundaryWord q (q/2-1)))
    let solution := normalized.map (unscaleBoundaryWord q)
    solution.length = B.card ∧ (∀ z ∈ solution, Fits w z) ∧
      ∀ i < B.card, ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
        ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp := by
  dsimp only
  intro hlen hformat hstage htable C D x₀ x hC hx₀ herror hx
  let band := PhaseCellBand.width p u
  let I := haloInterior s t band a b
  let B := haloBoundary s t band a b
  let cellTarget := boundaryHaloTarget p u target rhsExp B.card
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let rhs := fun i => (value q (C i)).re
  let Z := fun i => realPartWord (couplingRowField (2^15*p) q t u band a b false D C i)
  let rows := (bFoldOrder s B).map Z
  let normalized := bandSolveVec q W (naturalLineLc q K W B.card AZ)
    (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
    (rows.map (normalizeBoundaryWord q (q/2-1)))
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hθpos : 0 < (t : ℝ)/s-1 := lt_of_lt_of_le (by positivity : 0 < 1/(4*(p : ℝ))) hθ
  have hU : I∪B = haloVertices s a b := haloInterior_union_boundary s t band a b
  have hI := dominates_mono (realMatrix s t p u) Finset.univ I _ (Finset.subset_univ I) hdom
  let R := fun c => Classical.choose (solves_exists (realMatrix s t p u) I _ hμ hI c)
  have hR c : Solves (realMatrix s t p u) I (R c) c :=
    Classical.choose_spec (solves_exists (realMatrix s t p u) I _ hμ hI c)
  have hM := dominates_mono (realMatrix s t p u) Finset.univ (I∪B) _ (Finset.subset_univ _) hdom
  have hx' : Solves (realMatrix s t p u) (I∪B) x rhs := by rw [hU]; exact hx
  have hschur := boundary_exact_schur_solves (realMatrix s t p u) I B
    (haloInterior_disjoint_boundary s t band a b) _ hμ hM R hR x rhs hx'
  have hwidth' : q+couplingRowExponent rhsExp (stableInteriorExponent p rhsExp)
      (8*p+1) (couplingCountExponent p u)+2 ≤ w := by
    have h := stableInteriorResidual_width p u l cellTarget rhsExp
    dsimp only [cellTarget] at h
    simpa only [(boundaryHaloTarget_sizing p u l target rhsExp B.card).1,
      (boundaryHaloTarget_sizing p u l target rhsExp B.card).2.2] using h
  have hmag : ∀ i, |gv q (Z i).re| ≤ (2 : ℝ)^couplingRowExponent rhsExp
      (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv q (Z i).im| ≤ (2 : ℝ)^couplingRowExponent rhsExp
      (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) := by
    intro i
    have hn := haloResidual_norm_bound hp0 hst hαu hθpos hgap hbudget a b hdom C D hC x₀ hx₀ herror i
    exact ⟨(Complex.abs_re_le_norm _).trans hn,(Complex.abs_im_le_norm _).trans hn⟩
  have hresidual i := haloResidual_error_bound hp hst hα hwidth hαu hθ hgap hbudget hwidth'
    hdom C D hC x₀ hx₀ herror R hR i
  have hformatSol := boundary_residual_solution_format A p u l target rhsExp B W columns hp hA hlen
    hformat hstage rows (by simp [rows,bFoldOrder_length]) (by
      intro z hz; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz; exact hmag i)
  have hlenN : normalized.length = B.card := naturalLineSolve_length q K W B.card AZ _
    (by simp [rows,bFoldOrder_length])
  have hxBound : ∀ i ∈ B, ‖(x i : ℂ)‖ ≤ 16*(p : ℝ)*(2 : ℝ)^rhsExp := by
    intro i hi
    have h := solves_bound (realMatrix s t p u) (I∪B) _ hμ hM x rhs hx' ((2 : ℝ)^rhsExp)
      (fun k _ => (Complex.abs_re_le_norm _).trans (hC k)) i (Finset.mem_union_right I hi)
    rw [div_div_eq_mul_div,div_one] at h
    rw [Complex.norm_real,Real.norm_eq_abs]
    nlinarith only [h,show (0 : ℝ) ≤ (p : ℝ)*(2 : ℝ)^rhsExp by positivity]
  refine ⟨hformatSol.1,hformatSol.2,?_⟩
  intro i hi
  have hiN : i < normalized.length := by rw [hlenN]; exact hi
  have hget : (normalized.map (unscaleBoundaryWord q)).getD i 0 = unscaleBoundaryWord q (normalized.getD i 0) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hiN),List.getD_eq_getElem _ _ hiN,List.getElem_map]
  have hacc := boundary_unscaled_solve_target_of_rhs_budget A p u l target rhsExp B W columns hp hA hlen
    Z hformat hstage (run (realMatrix s t p u) (I∪B) I.toList).1
    (fun k => (x k : ℂ)) (fun k => (residual (realMatrix s t p u) I R rhs k : ℂ))
    (by simpa only [Complex.ofReal_re] using hschur)
    (by intro k hk; simp [Complex.ofReal_im])
    (haloResidualError p u q rhsExp cellTarget) (boundaryHaloTarget_residual_budget p u l target rhsExp B.card)
    (by simpa only [hU] using htable) (fun k _ => hmag k) (fun k _ => hresidual k) hxBound i hi
  have hacc' : ‖value q ((normalized.map (unscaleBoundaryWord q)).getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤
      3/(2 : ℝ)^target := by
    rw [hget]
    simpa only [normalized,rows,bFoldOrder,List.map_map,Function.comp_def] using hacc
  exact ⟨hacc',boundary_computed_solution_magnitude p rhsExp target hp0 _ _
    (hxBound _ (bFoldAt_mem s B i hi)) hacc'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
