module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRankError
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolutionBounds

/-! Componentwise accuracy of the actual Gaussian boundary solution list. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.BandList IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem boundary_solution_part_error (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (W : ℕ) (columns : List (ZMod s → GaussianInt))
    (hp : 2 ≤ p) (hA : 4 ≤ A) (hlen : columns.length = B.card) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    ∀ (π : GaussianInt → ℤ), π 0 = 0 →
    (∀ b, (bandSolveVec q W (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) b).map π =
        lineSolveZ q K W B.card AZ (b.map π)) →
    ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
      (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ (rhs : List GaussianInt), rhs.length = B.card →
    (∀ i < B.card, |gv q (π (rhs.getD i 0))| ≤ 1/2) →
    ∀ (R : Matrix (ZMod s) (ZMod s) ℝ) (x b : ℕ → ℝ), Solves (fun i j => R (bFoldAt s B i) (bFoldAt s B j)) (Finset.range B.card) x b →
    ∀ (ε δ X : ℝ), 0 ≤ X →
    (∀ i ∈ B, ∀ j ∈ B,
      |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j - R i j| ≤ ε) →
    (∀ i ∈ Finset.range B.card, |gv q (π (rhs.getD i 0)) - b i| ≤ δ) →
    (∀ i ∈ Finset.range B.card, |x i| ≤ X) →
    ∀ i < B.card, |gv q (π ((bandSolveVec q W (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) rhs).getD i 0)) - x i| ≤
      62000*(2*(p : ℝ))^3*(B.card : ℝ)^2*
        ((1/2^q : ℝ)*(1+60*3/(1/(32*(p : ℝ)))^2)) +
      (δ + ((B.card : ℝ)*ε)*X)/(1/(8*(2*(p : ℝ)))) := by
  dsimp only
  intro π hπ0 hsolve hformat hstage rhs hlenR hbound R x b hx ε δ X hX herror hrhs hsol i hi
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  have hb : (rhs.map π).length = B.card := by simp [hlenR]
  have hbound' : ∀ i < B.card, |gv q ((rhs.map π).getD i 0)| ≤ 1/2 := by
    intro i hi
    rw [← proj_getD π hπ0]
    exact hbound i hi
  have hrhs' : ∀ i ∈ Finset.range B.card, |gv q ((rhs.map π).getD i 0) - b i| ≤ δ := by
    intro i hi
    rw [← proj_getD π hπ0]
    exact hrhs i hi
  have h := boundary_rank_allocated_error A p u l target rhsExp B W columns hp hA hlen
    hformat hstage (rhs.map π) hb hbound' R x b hx ε δ X hX herror hrhs' hsol i hi
  rw [← hsolve rhs, ← proj_getD π hπ0] at h
  exact h

theorem boundary_solution_norm_error (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
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
    ∀ (rhs : List GaussianInt), rhs.length = B.card →
    (∀ i < B.card, |gv q (rhs.getD i 0).re| ≤ 1/2 ∧ |gv q (rhs.getD i 0).im| ≤ 1/2) →
    ∀ (R : Matrix (ZMod s) (ZMod s) ℝ) (x b : ℕ → ℂ),
    Solves (fun i j => R (bFoldAt s B i) (bFoldAt s B j)) (Finset.range B.card)
      (fun i => (x i).re) (fun i => (b i).re) →
    Solves (fun i j => R (bFoldAt s B i) (bFoldAt s B j)) (Finset.range B.card)
      (fun i => (x i).im) (fun i => (b i).im) →
    ∀ (ε δ X : ℝ), 0 ≤ X →
    (∀ i ∈ B, ∀ j ∈ B,
      |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j - R i j| ≤ ε) →
    (∀ i ∈ Finset.range B.card, ‖value q (rhs.getD i 0) - b i‖ ≤ δ) →
    (∀ i ∈ Finset.range B.card, ‖x i‖ ≤ X) →
    ∀ i < B.card, ‖value q ((bandSolveVec q W (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) rhs).getD i 0) - x i‖ ≤
      2 * (62000*(2*(p : ℝ))^3*(B.card : ℝ)^2*
        ((1/2^q : ℝ)*(1+60*3/(1/(32*(p : ℝ)))^2)) +
      (δ + ((B.card : ℝ)*ε)*X)/(1/(8*(2*(p : ℝ))))) := by
  dsimp only
  intro hformat hstage rhs hlenR hbound R x b hxre hxim ε δ X hX herror hrhs hsol i hi
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  have hre := boundary_solution_part_error A p u l target rhsExp B W columns hp hA hlen
    (·.re) rfl (naturalLineSolve_re q K W B.card AZ) hformat hstage rhs hlenR
    (fun i hi => (hbound i hi).1) R (fun i => (x i).re) (fun i => (b i).re) hxre
    ε δ X hX herror
    (fun i hi => by simpa [value,gv] using (Complex.abs_re_le_norm _).trans (hrhs i hi))
    (fun i hi => (Complex.abs_re_le_norm _).trans (hsol i hi)) i hi
  have him := boundary_solution_part_error A p u l target rhsExp B W columns hp hA hlen
    (·.im) rfl (naturalLineSolve_im q K W B.card AZ) hformat hstage rhs hlenR
    (fun i hi => (hbound i hi).2) R (fun i => (x i).im) (fun i => (b i).im) hxim
    ε δ X hX herror
    (fun i hi => by simpa [value,gv] using (Complex.abs_im_le_norm _).trans (hrhs i hi))
    (fun i hi => (Complex.abs_im_le_norm _).trans (hsol i hi)) i hi
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (value q ((bandSolveVec q W (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) rhs).getD i 0) - x i)
  simp only [Complex.sub_re,Complex.sub_im] at hnorm
  change _ ≤ 2 * _
  simpa only [value,gv] using hnorm.trans (add_le_add hre him) |>.trans_eq (by ring)

/-- Reindex a boundary system in the exact order used by the factorizer. -/
theorem boundary_solves_rank {s : ℕ} [NeZero s] (B : Finset (ZMod s))
    (R : Matrix (ZMod s) (ZMod s) ℝ) (x b : ZMod s → ℝ) (hx : Solves R B x b) :
    Solves (fun i j => R (bFoldAt s B i) (bFoldAt s B j)) (Finset.range B.card)
      (fun i => x (bFoldAt s B i)) (fun i => b (bFoldAt s B i)) := by
  intro i hi
  exact (bFoldAt_sum B (fun j => R (bFoldAt s B i) j * x j)).trans
    (hx _ (bFoldAt_mem s B i (Finset.mem_range.mp hi)))

theorem boundary_solution_coordinate_error (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
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
    ∀ (rhs : List GaussianInt), rhs.length = B.card →
    (∀ i < B.card, |gv q (rhs.getD i 0).re| ≤ 1/2 ∧ |gv q (rhs.getD i 0).im| ≤ 1/2) →
    ∀ (R : Matrix (ZMod s) (ZMod s) ℝ) (x b : ZMod s → ℂ),
    Solves R B
      (fun i => (x i).re) (fun i => (b i).re) →
    Solves R B
      (fun i => (x i).im) (fun i => (b i).im) →
    ∀ (ε δ X : ℝ), 0 ≤ X →
    (∀ i ∈ B, ∀ j ∈ B,
      |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j - R i j| ≤ ε) →
    (∀ i ∈ Finset.range B.card, ‖value q (rhs.getD i 0) - b (bFoldAt s B i)‖ ≤ δ) →
    (∀ i ∈ B, ‖x i‖ ≤ X) →
    ∀ i < B.card, ‖value q ((bandSolveVec q W (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) rhs).getD i 0) - x (bFoldAt s B i)‖ ≤
      2 * (62000*(2*(p : ℝ))^3*(B.card : ℝ)^2*
        ((1/2^q : ℝ)*(1+60*3/(1/(32*(p : ℝ)))^2)) +
      (δ + ((B.card : ℝ)*ε)*X)/(1/(8*(2*(p : ℝ))))) := by
  dsimp only
  intro hformat hstage rhs hlenR hbound R x b hxre hxim ε δ X hX herror hrhs hsol i hi
  exact boundary_solution_norm_error A p u l target rhsExp B W columns hp hA hlen
    hformat hstage rhs hlenR hbound R (fun i => x (bFoldAt s B i)) (fun i => b (bFoldAt s B i))
    (boundary_solves_rank B R _ _ hxre) (boundary_solves_rank B R _ _ hxim)
    ε δ X hX herror hrhs
    (fun j hj => hsol _ (bFoldAt_mem s B j (Finset.mem_range.mp hj))) i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
