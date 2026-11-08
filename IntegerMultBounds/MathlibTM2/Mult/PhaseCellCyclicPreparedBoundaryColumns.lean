module

public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalStability
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRankStability
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetOwnedRecoveryJob

/-! The joint cyclic Schur matrix feeds the existing prepared band-factor contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open scoped BigOperators
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
variable {s t p u l : ℕ} [NeZero s] {alpha gap : ℝ}

theorem cyclicPreparedBoundaryColumns_of_accurate (axis : RecoveryAxisBounds s t p u l alpha gap)
    (a n : ℕ) (ha : a < s) (hn : n ≤ s) (A bits q w : ℕ)
    (columns : List (ZMod s → GaussianInt)) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let W := 24*band+1
    let S := (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
      (cyclicPrincipalInterior s t band a n).toList).1
    columns.length = B.card → ColumnFamilyFormat w columns →
    ColumnFamilyAccurate A q w B S (1/(2 : ℝ)^bits) columns →
    PreparedBoundaryColumns A p bits q w W B columns := by
  dsimp only
  intro hlen hformat hcolumns
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let W := 24*band+1
  let S := (SchurDominance.run (realMatrix s t p u) (cyclicPrincipalVertices s a n)
    (cyclicPrincipalInterior s t band a n).toList).1
  let : NeZero t := ⟨Nat.ne_of_gt ((NeZero.pos s).trans axis.hst)⟩
  have hmu : (0 : ℝ) < 1/(8*(p : ℝ)) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have := axis.hp; omega)
    positivity
  have hmass (i : ZMod s) : ∑ j, |realMatrix s t p u i j| ≤ (2 : ℝ) := by
    calc
      _ = ∑ j, realMatrix s t p u i j := by
        apply Finset.sum_congr rfl
        intro j _
        apply abs_of_nonneg
        unfold realMatrix
        exact_mod_cast matrix_nonneg s t p u i j
      _ ≤ 2 := matrix_row_sum_le_two axis.hst axis.hα p u axis.hp axis.hpacket axis.hαu axis.hθ axis.hgap axis.hbudget i
  have hstage : StageInv S B (1/(8*(p : ℝ))) 2 :=
    cyclicPrincipal_schur_stageInv p u a n _ _ hmu axis.hdom hmass
  have hentry := computedBoundaryTable_band_error A q w B W columns hlen S (1/(2 : ℝ)^bits)
    (by positivity) (fun _ hi _ hj h => cyclicPrincipal_schur_foldBRel axis.hst p u a n ha hn hi hj h) hcolumns
  have hstable := boundaryTable_stageInv B W (computedBoundaryTable A q w B columns) S _ _ _ hstage hentry
  exact ⟨hlen,hformat,factorRankMatrix_stageInv A q w B W columns _ _ hstable⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
