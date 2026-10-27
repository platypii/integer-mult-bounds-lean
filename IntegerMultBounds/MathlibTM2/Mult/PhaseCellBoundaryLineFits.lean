module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryLineParts

/-! Every intermediate RHS record of the computed boundary solve fits its allocated word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.BandList IntegerMultBounds.MathlibTM2.Mult.Sizes

structure BoundaryRhsFits (q w W N : ℕ) (Lc Uc : List (List ℤ)) (rcs : List ℤ)
    (b : List GaussianInt) : Prop where
  forward : ∀ j < N, Fits w ((bandPend q Lc (b ++ List.replicate W 0) j).headD 0)
  backward : ∀ j < N, Fits w ((bandPendB q Uc rcs
    ((fwdZC q Lc (b ++ List.replicate W 0)).reverse ++ List.replicate W 0) j).headD 0)
  output : ∀ j < N, Fits w (tdivN q ((bandPendB q Uc rcs
    ((fwdZC q Lc (b ++ List.replicate W 0)).reverse ++ List.replicate W 0) j).headD 0 *
      ⟨rcs.getD j 0,0⟩))
  solution : ∀ a ∈ bandSolveVec q W Lc Uc rcs b, Fits w a

/-- All RHS fit premises of the triangular runtime follow from the constructed
matrix invariant and the scaled input bound, including the backward numerators. -/
theorem boundary_line_allocated_rhsFits (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
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
    ∀ (b : List GaussianInt), b.length = B.card →
    (∀ a ∈ b, |gv q a.re| ≤ 1/2 ∧ |gv q a.im| ≤ 1/2) →
    BoundaryRhsFits q w W B.card (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ) b := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  intro hformat hstage b hb hbin
  have hre := boundary_line_part A p u l target rhsExp B W columns hp hA hlen hformat hstage b hb
    (·.re) rfl (fwdZC_re q) (naturalLineSolve_re q K W B.card AZ)
    (fun _ => rfl) (fun z c => mul_real_re z c) (fun a ha => (hbin a ha).1)
  have him := boundary_line_part A p u l target rhsExp B W columns hp hA hlen hformat hstage b hb
    (·.im) rfl (fwdZC_im q) (naturalLineSolve_im q K W B.card AZ)
    (fun _ => rfl) (fun z c => mul_real_im z c) (fun a ha => (hbin a ha).2)
  have hbits : 4*p+2*Nat.size B.card+36 ≤ q := factor_execution_bits p u l target rhsExp B.card
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hwidth : (4*(8*(p : ℝ)+2))*(2 : ℝ)^q < (2 : ℝ)^(w-1) := by
    have hc : 6/(1/(32*(p : ℝ)))+1 = 192*p+1 := by field_simp; ring
    have hbig := factor_record_width_budget p q (by omega) (by omega : p+2 ≤ q)
    rw [hc,← hw] at hbig
    exact (mul_le_mul_of_nonneg_right (by linarith : 4*(8*(p : ℝ)+2) ≤ 192*p+1)
      (by positivity : (0 : ℝ) ≤ 2^q)).trans_lt hbig
  have hfit (z : GaussianInt) (hr : |gv q z.re| ≤ 4*(8*(p : ℝ)+2))
      (hi : |gv q z.im| ≤ 4*(8*(p : ℝ)+2)) : Fits w z := fitsC_of_gv hr hi hwidth
  refine ⟨fun j hj => ?_,fun j hj => ?_,fun j hj => ?_,fun a ha => ?_⟩
  · apply hfit
    · exact (hre.1 j hj).trans (by linarith)
    · exact (him.1 j hj).trans (by linarith)
  · exact hfit _ (hre.2.1 j hj) (him.2.1 j hj)
  · apply hfit
    · exact (hre.2.2.1 j hj).trans (by linarith)
    · exact (him.2.2.1 j hj).trans (by linarith)
  · apply hfit
    · exact (hre.2.2.2 a ha).trans (by linarith)
    · exact (him.2.2.2 a ha).trans (by linarith)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
