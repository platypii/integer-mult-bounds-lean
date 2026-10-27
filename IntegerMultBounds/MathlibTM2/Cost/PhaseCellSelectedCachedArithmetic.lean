module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedArithmetic
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyHaloInteriorGeometryCost

/-! Apply cached-arithmetic bounds to the inverse caller's actual precision.
The geometry and target hypotheses derive the width; padded length is explicit. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem inverseCachedArithmetic_selected_fast_le (cl ct cG cr : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p u l target s t a b : ℕ, ∀ [NeZero s],
      1 ≤ p → PhaseCellBand.width p u ≤ s → l ≤ cl*p → target ≤ ct*p →
      Nat.size (2*s+1) ≤ cG*p → 2^l ≤ cr*p →
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let stage := initialSchurTarget p u bits 2
      let w := executionWidth p l stage 2
      ((cachedBatchCoordinateCost p l stage 2+44*w : ℕ) : ℝ) ≤ C*(p : ℝ)^(129/128 : ℝ) ∧
      (cachedBatchCellCost p l stage 2 : ℝ) ≤ C*(2^l : ℕ)*(p : ℝ)^(129/128 : ℝ) := by
  let cw := 16*cl+8*ct+16*cG+680
  obtain ⟨K,hK,hcoord⟩ := cachedBatchCoordinate_fast_le cl cw
  obtain ⟨D,hD,hcell⟩ := cachedBatchCell_fast_le cl cw cr
  refine ⟨K+44*(cw : ℝ)+D,by positivity,?_⟩
  intro p u l target s t a b _ hp hband hl ht hgeometry hr
  dsimp only
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let stage := initialSchurTarget p u bits 2
  let w := executionWidth p l stage 2
  have hN : N ≤ s := by simpa using Finset.card_le_univ (s := haloBoundary s t (PhaseCellBand.width p u) a b)
  have hNlog : Nat.size N ≤ cG*p := (Nat.size_le_size (by omega : N ≤ 2*s+1)).trans hgeometry
  have hBlog : Nat.size (2*PhaseCellBand.width p u+1) ≤ cG*p :=
    (Nat.size_le_size (by omega)).trans hgeometry
  have hwidth : w ≤ cw*p := by
    have hw := inverseExecutionWidth_le p l target N (PhaseCellBand.width p u) cl ct cG cG hp hl ht hNlog hBlog
    change 8*executionExponent p l stage 2+8 ≤ cw*p
    rw [← inverseExecutionExponent_eq]
    dsimp only [cw]
    nlinarith only [hw]
  have hc := hcoord p l stage 2 hp hl hwidth
  have hd := hcell p l stage 2 hp hl hwidth hr
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hMp : 0 ≤ (p : ℝ)^(129/128 : ℝ) := by positivity
  have hpPow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hwR : (w : ℝ) ≤ (cw : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
    calc
      _ ≤ (cw : ℝ)*p := by exact_mod_cast hwidth
      _ ≤ _ := mul_le_mul_of_nonneg_left hpPow (Nat.cast_nonneg cw)
  constructor
  · push_cast
    nlinarith only [hc,hwR,mul_nonneg hD hMp]
  · have hmore : 0 ≤ (K+44*(cw : ℝ))*(2^l : ℕ)*(p : ℝ)^(129/128 : ℝ) := by positivity
    nlinarith only [hd,hmore]

end IntegerMultBounds.MathlibTM2.Cost
