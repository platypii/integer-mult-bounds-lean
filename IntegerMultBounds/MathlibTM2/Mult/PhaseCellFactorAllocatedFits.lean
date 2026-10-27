module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorStateFits
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPrecisionBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorNewtonBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorStabilityBudget

/-! Canonical precision and logarithmic Newton count discharge every factor-state fit condition. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Fast

variable {s : ℕ} [NeZero s]

theorem factorIntegerState_allocated_fits (A p u l target rhsExp : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hA : 4 ≤ A) (hp : 2 ≤ p) (hlen : columns.length = B.card) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
      (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ m < B.card, FacFits w q (factorNewtonSteps p q)
      (facState q (factorNewtonSteps p q) (factorIntegerRows (factorWindowValues B W columns))
        (factorIntegerRows (factorInputValues B W B.card columns)) m) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  intro hformat hstage m hm
  have hbits : 4*p+2*Nat.size B.card+36 ≤ q := factor_execution_bits p u l target rhsExp B.card
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hq : 2 ≤ q := by omega
  have hinv := boundaryFactor_stageInv_allocated _ p target rhsExp B.card hp hstage
  apply factorIntegerState_fits A q w (factorNewtonSteps p q) B W columns hlen hformat hA
    (by rw [hw]; omega) p hp hq hinv (1/(32*(p : ℝ))) (by positivity)
  · apply le_of_eq
    field_simp
    ring
  · exact factor_roundoff_budget p q (by omega) (by omega)
  · exact factorNewtonSteps_budget p q (by omega)
  · exact factor_stage_roundoff_budget p q B.card (by omega) hbits
  · rw [hw]
    exact factor_record_width_budget p q (by omega) (by omega)
  · exact hm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
