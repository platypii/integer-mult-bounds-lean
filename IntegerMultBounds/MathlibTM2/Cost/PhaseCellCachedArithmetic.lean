module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchCost
public import IntegerMultBounds.MathlibTM2.Cost.ChirpLogGrowth
public import IntegerMultBounds.MathlibTM2.Cost.MatchConv

/-! Uniform multiplication allowances for the executed cached interior arithmetic,
including packed-record conversions and all per-coordinate tape work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Schedule IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- A cell record with linear precision, width and padded length costs its length times M(p). -/
theorem phaseCell_rpRec_fast_le (cq cl cw cr : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q l w : ℕ, 1 ≤ p → 1 ≤ q →
      q ≤ cq*p → l ≤ cl*p → w ≤ cw*p → 2^l ≤ cr*p →
      (rpRecBound q l w : ℝ) ≤ C*(2^l : ℕ)*(p : ℝ)^(129/128 : ℝ) := by
  let c := 4*cq+2*cl+4*cw
  obtain ⟨K,hK,hring⟩ := chirp_ringBound_le (c*cr) c
  let F := 640*cw+1812
  refine ⟨3*K+(F : ℝ),by positivity,?_⟩
  intro p q l w hp hq hqp hl hw hr
  let r := 2^l
  let N := wOf q l w*r
  have hv : wOf q l w ≤ c*p := by
    have h := mt_cv_wOf_le q l w hq
    dsimp only [c]
    nlinarith only [h,hqp,hl,hw]
  have hN : N ≤ c*r*p := by
    calc
      N ≤ (c*p)*r := Nat.mul_le_mul_right r hv
      _ = _ := by ring
  have hquad : N ≤ (c*cr)*p^2 := by
    have h := Nat.mul_le_mul_left (c*p) hr
    dsimp only [N,r] at *
    nlinarith only [hN,h]
  have hring' := hring p r N hp Nat.one_le_two_pow hN hquad
  have hrp : r ≤ r*p := Nat.le_mul_of_pos_right _ hp
  have hpos : 1 ≤ r*p := Nat.mul_pos Nat.one_le_two_pow hp
  have hrw : r*w ≤ cw*(r*p) := by nlinarith only [Nat.mul_le_mul_left r hw]
  have hformat : 640*(r*w)+1200*r+612 ≤ F*(r*p) := by
    dsimp only [F]
    nlinarith only [hrp,hpos,hrw]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hformatR : 640*((r : ℝ)*w)+1200*(r : ℝ)+612 ≤
      (F : ℝ)*(r : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
    calc
      _ ≤ (F : ℝ)*(r : ℝ)*p := by exact_mod_cast (by simpa only [Nat.mul_assoc] using hformat : 640*(r*w)+1200*r+612 ≤ F*r*p)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpPow (by positivity)
  have hcast : (rpRecBound q l w : ℝ) =
      3*(rpRingBound N : ℝ)+(640*((r : ℝ)*w)+1200*(r : ℝ)+612) := by
    dsimp only [rpRecBound,N,r]
    push_cast
    ring
  rw [hcast]
  calc
    _ ≤ 3*(K*(r : ℝ)*(p : ℝ)^(129/128 : ℝ))+
        (F : ℝ)*(r : ℝ)*(p : ℝ)^(129/128 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hring' (by norm_num)) hformatR
    _ = _ := by dsimp only [r]; ring

/-- The cached coordinate ledger includes scalar products, normalization and tape movement. -/
theorem cachedBatchCoordinate_fast_le (cl cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p l target rhsExp : ℕ, 1 ≤ p → l ≤ cl*p →
      executionWidth p l target rhsExp ≤ cw*p →
      (cachedBatchCoordinateCost p l target rhsExp : ℝ) ≤ C*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hmul⟩ := chirp_rmul_le cw
  let F := 839*cw+8*cl+441
  refine ⟨3*K+(F : ℝ),by positivity,?_⟩
  intro p l target rhsExp hp hl hw
  let w := executionWidth p l target rhsExp
  have hwpos : 1 ≤ w := by dsimp [w,executionWidth]; omega
  have hE : executionExponent p l target rhsExp ≤ w := by dsimp [w,executionWidth]; omega
  have hlinear : 835*w+4*(inputExponent p (sourceExponent l target rhsExp)+2*l+2)+433 ≤ F*p := by
    change 835*w+4*(executionExponent p l target rhsExp+2*l+2)+433 ≤ F*p
    dsimp only [F]
    nlinarith only [hw,hE,hl,hp]
  have hmul' := hmul p w hp hwpos hw
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hlinearR : ((835*w+4*(inputExponent p (sourceExponent l target rhsExp)+2*l+2)+433 : ℕ) : ℝ) ≤
      (F : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
    calc
      _ ≤ (F : ℝ)*p := by exact_mod_cast hlinear
      _ ≤ _ := mul_le_mul_of_nonneg_left hpPow (Nat.cast_nonneg F)
  have hcost : (cachedBatchCoordinateCost p l target rhsExp : ℝ) =
      3*(rmulCost w : ℝ)+((835*w+4*(inputExponent p (sourceExponent l target rhsExp)+2*l+2)+433 : ℕ) : ℝ) := by
    dsimp only [cachedBatchCoordinateCost,w]
    push_cast
    ring
  rw [hcost]
  calc
    _ ≤ 3*(K*(p : ℝ)^(129/128 : ℝ))+(F : ℝ)*(p : ℝ)^(129/128 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hmul' (by norm_num)) hlinearR
    _ = _ := by ring

/-- Padded cell products, conversions and release clocks have a uniform per-cell allowance. -/
theorem cachedBatchCell_fast_le (cl cw cr : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p l target rhsExp : ℕ, 1 ≤ p → l ≤ cl*p →
      executionWidth p l target rhsExp ≤ cw*p → 2^l ≤ cr*p →
      (cachedBatchCellCost p l target rhsExp : ℝ) ≤ C*(2^l : ℕ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hrec⟩ := phaseCell_rpRec_fast_le cw cl cw cr
  let F := 248*cw+704
  refine ⟨4*K+(F : ℝ),by positivity,?_⟩
  intro p l target rhsExp hp hl hw hr
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let r := 2^l
  have hq : 1 ≤ q := by
    dsimp [q,executionPrecision,executionExponent,inputExponent,sourceExponent]
    omega
  have hqp : q ≤ cw*p := by
    have hqw : q ≤ w := by dsimp [q,w,executionPrecision,executionWidth]; omega
    exact hqw.trans hw
  have hrec' := hrec p q l w hp hq hqp hl hw hr
  have hrp : 1 ≤ r*p := Nat.mul_pos Nat.one_le_two_pow hp
  have hrw : r*w ≤ cw*(r*p) := by nlinarith only [Nat.mul_le_mul_left r hw]
  have hlinear : 704+248*(r*w) ≤ F*(r*p) := by
    dsimp only [F]
    nlinarith only [hrp,hrw]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hlinearR : ((704+248*(r*w) : ℕ) : ℝ) ≤ (F : ℝ)*(r : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
    calc
      _ ≤ (F : ℝ)*(r : ℝ)*p := by exact_mod_cast (by simpa only [Nat.mul_assoc] using hlinear : 704+248*(r*w) ≤ F*r*p)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpPow (by positivity)
  have hcost : (cachedBatchCellCost p l target rhsExp : ℝ) =
      4*(rpRecBound q l w : ℝ)+((704+248*(r*w) : ℕ) : ℝ) := by
    dsimp only [cachedBatchCellCost,q,w,r]
    push_cast
    ring
  rw [hcost]
  calc
    _ ≤ 4*(K*(r : ℝ)*(p : ℝ)^(129/128 : ℝ))+(F : ℝ)*(r : ℝ)*(p : ℝ)^(129/128 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hrec' (by norm_num)) hlinearR
    _ = _ := by dsimp only [r]; ring

end IntegerMultBounds.MathlibTM2.Cost
