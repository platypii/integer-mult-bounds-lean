module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryScaleError

/-! Accuracy and half-unit bounds for the actual folded, normalized residual list. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.Sizes

/-- The list passed to the physical solve, with bounds derived from retained residual data. -/
theorem boundary_normalized_rhs_spec (p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (C : ZMod s → GaussianInt) (c : ZMod s → ℂ) (δ : ℝ) :
    let q := executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p target rhsExp B.card) 2) 2
    let rhs := ((List.range B.card).map (fun j => C (bFoldAt s B j))).map
      (normalizeBoundaryWord q (q/2-1))
    (∀ j ∈ B, |gv q (C j).re| ≤ (2 : ℝ)^couplingRowExponent rhsExp
        (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u) ∧
      |gv q (C j).im| ≤ (2 : ℝ)^couplingRowExponent rhsExp
        (stableInteriorExponent p rhsExp) (8*p+1) (couplingCountExponent p u)) →
    (∀ j ∈ B, ‖value q (C j) - c j‖ ≤ δ) →
    rhs.length = B.card ∧
    (∀ i < B.card, |gv q (rhs.getD i 0).re| ≤ 1/2 ∧ |gv q (rhs.getD i 0).im| ≤ 1/2) ∧
    ∀ i < B.card,
      ‖value q (rhs.getD i 0) - c (bFoldAt s B i)/(2 : ℂ)^(q/2+1)‖ ≤
        2/(2 : ℝ)^q + δ/(2 : ℝ)^(q/2+1) := by
  dsimp only
  let q := executionPrecision p l (initialSchurTarget p u
    (boundaryTableBits p target rhsExp B.card) 2) 2
  let rhs := ((List.range B.card).map (fun j => C (bFoldAt s B j))).map
    (normalizeBoundaryWord q (q/2-1))
  intro hmag herror
  obtain ⟨hq,heven,-,-⟩ := boundary_normalization_precision p u l target rhsExp B.card
  change 2 ≤ q at hq
  change q%2 = 0 at heven
  have hsplit : q = q/2+(q/2-1)+1 := by omega
  have hget (i : ℕ) (hi : i < B.card) :
      rhs.getD i 0 = normalizeBoundaryWord q (q/2-1) (C (bFoldAt s B i)) := by
    simp [rhs,hi]
  refine ⟨by simp,fun i hi => ?_,fun i hi => ?_⟩
  · rw [hget i hi]
    exact normalizeBoundaryWord_bound q (q/2) (q/2-1) hsplit _
      (boundary_residual_normalization_bound p u l target rhsExp B.card _
        (hmag _ (bFoldAt_mem s B i hi)))
  · rw [hget i hi]
    exact boundary_normalized_rhs_error q (q/2) (q/2-1) hsplit _ _ δ
      (herror _ (bFoldAt_mem s B i hi))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
