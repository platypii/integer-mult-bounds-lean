module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryLineParts

/-! Expose the computed solution's component bounds for exact unscaling. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.BandList

theorem naturalLineSolve_length (q K W N : ℕ) (AZ : ℕ → ℕ → ℤ) (b : List GaussianInt)
    (hb : b.length = N) :
    (bandSolveVec q W (naturalLineLc q K W N AZ) (naturalLineUc q K W N AZ)
      (naturalLineRcs q K W N AZ) b).length = N := by
  obtain ⟨hLc,hUc,hrcs⟩ := naturalLineTables_lengths q K W N AZ
  have hf : (fwdZC q (naturalLineLc q K W N AZ) (b++List.replicate W 0)).length = N := by
    rw [length_fwdZC q _ _ (by simp only [List.length_append,List.length_replicate,hb]; omega),hLc]
  rw [bandSolveVec,List.length_reverse,length_bwdZC q _ _ _ (by omega) (by simp [hf]; omega),hUc]

theorem boundary_line_allocated_solution_bounds (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
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
    ∀ (b : List GaussianInt), b.length = B.card →
    (∀ z ∈ b, |gv q z.re| ≤ 1/2 ∧ |gv q z.im| ≤ 1/2) →
    ∀ z ∈ bandSolveVec q W (naturalLineLc q K W B.card AZ) (naturalLineUc q K W B.card AZ)
      (naturalLineRcs q K W B.card AZ) b, |gv q z.re| ≤ 8*p+1 ∧ |gv q z.im| ≤ 8*p+1 := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  intro hformat hstage b hb hbin
  have hre := boundary_line_part A p u l target rhsExp B W columns hp hA hlen hformat hstage b hb
    (·.re) rfl (fwdZC_re q) (naturalLineSolve_re q K W B.card AZ)
    (fun _ => rfl) (fun z c => mul_real_re z c) (fun z hz => (hbin z hz).1)
  have him := boundary_line_part A p u l target rhsExp B W columns hp hA hlen hformat hstage b hb
    (·.im) rfl (fwdZC_im q) (naturalLineSolve_im q K W B.card AZ)
    (fun _ => rfl) (fun z c => mul_real_im z c) (fun z hz => (hbin z hz).2)
  intro z hz
  exact ⟨hre.2.2.2 z hz,him.2.2.2 z hz⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
