module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryLineSizes
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalLineTables

/-! Reciprocal records of the computed boundary solve stay uniformly positive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.Sizes

/-- A pivot at most three and a reciprocal error at most `1/12` give the lower
bound needed to recover a backward head from its rounded output. -/
theorem newtonZ_quarter_le (q K : ℕ) (hq : 2 ≤ q) (c : ℤ) (β : ℝ) (hβ : 0 < β)
    (hlo : β ≤ gv q c) (hhi : gv q c ≤ 3)
    (hηβ : 5*(1/2^q : ℝ) ≤ 2*(β/4)/9)
    (hK : (1-β/4/2)^(2^K) ≤ 3*(5*(1/2^q : ℝ))/(β/4))
    (herr : 60*(1/2^q : ℝ)/β^2 ≤ 1/12) : 1/4 ≤ gv q (newtonZ q c K) := by
  rw [← newtonZ_eq q hq c K]
  have h := NewtonRecip.newtonR_recip (rdP q) _ (rdP_err q) β (gv q c) hβ hlo hhi hηβ K hK
  have hc0 : 0 < gv q c := lt_of_lt_of_le hβ hlo
  have h13 : 1/3 ≤ 1/gv q c := one_div_le_one_div_of_le hc0 hhi
  have := (abs_le.mp h).1
  linarith

theorem boundary_line_rcs_lower (A p u l target rhsExp : ℕ) {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (W : ℕ) (columns : List (ZMod s → GaussianInt))
    (hp : 2 ≤ p) (hA : 4 ≤ A) (hlen : columns.length = B.card) :
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let K := factorNewtonSteps p q
    ColumnFamilyFormat w columns →
    StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card)
      (1/(8*(p : ℝ))-(B.card : ℝ)*(1/(2 : ℝ)^bits))
      (2+(B.card : ℝ)*(1/(2 : ℝ)^bits)) →
    ∀ j < B.card, 1/4 ≤ gv q ((naturalLineRcs q K W B.card
      (factorRankIntegerMatrix B W columns)).getD j 0) := by
  dsimp only
  let bits := boundaryTableBits p target rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let K := factorNewtonSteps p q
  let AZ := factorRankIntegerMatrix B W columns
  let β : ℝ := 1/(32*(p : ℝ))
  intro hformat hstage j hj
  have hbits : 4*p+2*Nat.size B.card+36 ≤ q := factor_execution_bits p u l target rhsExp B.card
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hq : 2 ≤ q := by omega
  have hwpos : 1 ≤ w := by omega
  have hinv := boundaryFactor_stageInv_allocated _ p target rhsExp B.card hp hstage
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβp : β ≤ 1/(8*(2*(p : ℝ)))/2 := by dsimp [β]; apply le_of_eq; field_simp; ring
  have hηβ := factor_roundoff_budget p q (by omega) (by omega : p+12 ≤ q)
  have hK := factorNewtonSteps_budget p q (by omega)
  have hsmall := factor_stage_roundoff_budget p q B.card (by omega) hbits
  have hm : B.card-1-j < B.card := by omega
  obtain ⟨hpiv,-⟩ := factorIntegerStage_sizes A q w K B W columns hlen hformat hA hwpos p hp hq
    hinv β hβ hβp hηβ hK hsmall (B.card-1-j) hm
  let c := stgZ q K AZ (B.card-1-j) (B.card-1-j) (B.card-1-j)
  have hband := factorRankIntegerMatrix_band A q w B W columns hlen hformat hA hwpos
  have hfac := factorRowsZ_run q K W hq AZ hband B.card
  have he : (naturalLineRcs q K W B.card AZ).getD j 0 = newtonZ q c K := by
    rw [naturalLineRcs,hfac,List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_reverse]
    simp [winRowZ,List.range'_succ,c]
  rw [he]
  apply newtonZ_quarter_le q K hq c β hβ hpiv.1 hpiv.2 hηβ hK
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hs1 : (1 : ℝ) ≤ B.card := by exact_mod_cast (by omega : 1 ≤ B.card)
  have hη : (0 : ℝ) ≤ 1/2^q := by positivity
  have h1 : 60*(1/2^q : ℝ)/β^2 ≤ (1/2^q : ℝ)*(1+60*3/β^2) := by
    have : 0 ≤ (1/2^q : ℝ)*(60*2/β^2) := by positivity
    have e : (1/2^q : ℝ)*(1+60*3/β^2) =
        (1/2^q : ℝ)+60*(1/2^q : ℝ)/β^2+(1/2^q : ℝ)*(60*2/β^2) := by ring
    linarith
  have h2 : (12 : ℝ) ≤ 2^16*(2*(p : ℝ))^2*(B.card : ℝ)^2 := by
    have h4 : (1 : ℝ) ≤ (2*(p : ℝ))^2 := by nlinarith
    have h5 : (1 : ℝ) ≤ (B.card : ℝ)^2 := by nlinarith
    have := one_le_mul_of_one_le_of_one_le h4 h5
    nlinarith
  have h3 : 0 ≤ (1/2^q : ℝ)*(1+60*3/β^2) := by positivity
  have := mul_le_mul_of_nonneg_right h2 h3
  change 2^16*(2*(p : ℝ))^2*(B.card : ℝ)^2*((1/2^q : ℝ)*(1+60*3/β^2)) ≤ 1 at hsmall
  linarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
