module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPreparedBoundaryColumns
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidualBoundaryAccuracy

/-! The computed joint cyclic residual feeds the generic Schur accuracy theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance

theorem cyclicBoundary_solution_accuracy (A p u l target a n : ℕ)
    {s t : ℕ} [NeZero s] {alpha gap : ℝ}
    (axis : RecoveryAxisBounds s t p u l alpha gap) (ha : a < s) (hn : n ≤ s)
    (hA : 4 ≤ A) (columns : List (ZMod s → GaussianInt)) :
    let band := PhaseCellBand.width p u
    let I := cyclicPrincipalInterior s t band a n
    let B := cyclicPrincipalBoundary s t band a n
    let V := cyclicPrincipalVertices s a n
    let bits := boundaryTableBits p target 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 24*band+1
    let K := factorNewtonSteps p q
    let AZ := factorRankIntegerMatrix B W columns
    PreparedBoundaryColumns A p bits q w W B columns →
    ColumnFamilyAccurate A q w B (SchurDominance.run (realMatrix s t p u) V I.toList).1
      (1/(2 : ℝ)^bits) columns →
    ∀ (C : ZMod s → GaussianInt) (R : (ZMod s → ℝ) → ZMod s → ℝ)
      (x b : ZMod s → ℝ),
    (∀ c, Solves (realMatrix s t p u) I (R c) c) →
    Solves (realMatrix s t p u) V x b →
    (∀ i ∈ V, |b i| ≤ (2 : ℝ)^2) →
    (∀ i ∈ B, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent 2
      (stableInteriorExponent p 2) (8*p+1) (couplingCountExponent p u)) →
    (∀ i ∈ B, (C i).im = 0) →
    (∀ i ∈ B, |(value q (C i)).re-residual (realMatrix s t p u) I R b i| ≤
      (1/(2 : ℝ)^(recoveryTarget p bits+2))/(8*(p : ℝ))) →
    let normalized := bandSolveVec q W (naturalLineLc q K W B.card AZ)
      (naturalLineUc q K W B.card AZ) (naturalLineRcs q K W B.card AZ)
      (((List.range B.card).map (fun j => C (bFoldAt s B j))).map
        (normalizeBoundaryWord q (q/2-1)))
    let solution := normalized.map (unscaleBoundaryWord q)
    solution.length = B.card ∧ ∀ i < B.card,
      ‖value q (solution.getD i 0)-(x (bFoldAt s B i) : ℂ)‖ ≤ 3/(2 : ℝ)^target ∧
      ‖value q (solution.getD i 0)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2 := by
  dsimp only
  intro hprepared hcolumns C R x b hR hx hb hnorm hreal herr
  let band := PhaseCellBand.width p u
  let I := cyclicPrincipalInterior s t band a n
  let B := cyclicPrincipalBoundary s t band a n
  let V := cyclicPrincipalVertices s a n
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 24*band+1
  have hpartition : I ∪ B = V := Finset.union_sdiff_of_subset
    (cyclicPrincipalInterior_subset t band a n)
  have hIB : Disjoint I B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hj).2 hi
  have hdom : DominatesOn (realMatrix s t p u) (I ∪ B) (1/(8*(p : ℝ))) := by
    rw [hpartition]
    exact dominates_mono (realMatrix s t p u) Finset.univ V _ (Finset.subset_univ _) axis.hdom
  have htable := computedBoundaryTable_band_error A q w B W columns hprepared.length
    (SchurDominance.run (realMatrix s t p u) V I.toList).1 (1/(2 : ℝ)^bits) (by positivity)
    (fun _ hi _ hj h => cyclicPrincipal_schur_foldBRel axis.hst p u a n ha hn hi hj h)
    hcolumns
  apply boundary_residual_solution_accuracy A p u l target 2 B W columns axis.hp hA
    hprepared.length C hprepared.format hprepared.stage (realMatrix s t p u) I hIB hdom R hR x b
  · simpa only [hpartition] using hx
  · simpa only [hpartition] using hb
  · simpa only [hpartition] using htable
  · intro i hi
    exact ⟨(Complex.abs_re_le_norm _).trans (hnorm i hi),
      (Complex.abs_im_le_norm _).trans (hnorm i hi)⟩
  · exact hreal
  · intro i hi
    have hpR : (0 : ℝ) < 8*(p : ℝ) := by
      have hp := axis.hp
      have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      positivity
    simpa only [mul_comm] using (le_div_iff₀ hpR).mp (herr i hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
