module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedBoundary
public import IntegerMultBounds.MathlibTM2.Cost.ChirpLogGrowth

/-! Fast repeated boundary solves at the inverse caller's selected precision, with setup charged separately. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Factor setup is absent from this repeated solve allowance; the actual prepared kernel pays rows times bandwidth. -/
theorem preparedResidual_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q N W : ℕ, 1 ≤ p → 2*q+8 ≤ cw*p → 1 ≤ W →
      (preparedResidualSolveCost q (2*q+8) N W : ℝ) ≤ C*((N+1 : ℕ) : ℝ)*(W : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hproduct⟩ := chirp_rmul_le cw
  refine ⟨1000*(K+(cw : ℝ)+1),by positivity,?_⟩
  intro p q N W hp hwidth hW
  let w := 2*q+8
  have hw : 1 ≤ w := by dsimp [w]; omega
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hOne : (1 : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
  have hwidthR : (w : ℝ) ≤ (cw : ℝ)*(p : ℝ) := by exact_mod_cast hwidth
  have hwPow := hwidthR.trans (mul_le_mul_of_nonneg_left hpPow (Nat.cast_nonneg cw))
  have hscalar : ((rmulCost w+w+1 : ℕ) : ℝ) ≤ (K+(cw : ℝ)+1)*(p : ℝ)^(129/128 : ℝ) := by
    push_cast
    have hh := add_le_add (add_le_add (hproduct p w hp hw hwidth) hwPow) hOne
    simpa only [add_mul,one_mul] using hh
  have hkernel : (preparedResidualSolveCost q (2*q+8) N W : ℝ) ≤
      1000*((N+1 : ℕ) : ℝ)*(W : ℝ)*((rmulCost w+w+1 : ℕ) : ℝ) := by
    exact_mod_cast preparedResidualSolveCost_le q N W hW
  calc
    _ ≤ 1000*((N+1 : ℕ) : ℝ)*(W : ℝ)*((K+(cw : ℝ)+1)*(p : ℝ)^(129/128 : ℝ)) :=
      hkernel.trans (mul_le_mul_of_nonneg_left hscalar (by positivity))
    _ = _ := by ring

/-- Apply the repeated-kernel bound to the actual precision formula, rather than a separately supplied working width. -/
theorem preparedResidual_selected_fast_le (cl ct cN cB : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p l target N band : ℕ, 1 ≤ p →
      l ≤ cl*p → target ≤ ct*p → Nat.size N ≤ cN*p → Nat.size (2*band+1) ≤ cB*p →
      (preparedResidualSolveCost (4*inverseExecutionExponent p l target N band)
        (8*inverseExecutionExponent p l target N band+8) N (12*band+1) : ℝ) ≤
        C*((N+1 : ℕ) : ℝ)*((12*band+1 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := preparedResidual_fast_le (16*cl+8*ct+8*cN+8*cB+680)
  refine ⟨C,hC,?_⟩
  intro p l target N band hp hl ht hN hB
  have hw := inverseExecutionWidth_le p l target N band cl ct cN cB hp hl ht hN hB
  have heq : 2*(4*inverseExecutionExponent p l target N band)+8 =
      8*inverseExecutionExponent p l target N band+8 := by omega
  simpa only [heq] using hfast p (4*inverseExecutionExponent p l target N band) N (12*band+1)
    hp (by omega) (by omega)


/-- Ambient geometry bounds both precision bit counts and the actual boundary row work. -/
theorem preparedHaloResidual_selected_fast_le (cl ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p l target s t band a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → band ≤ s → l ≤ cl*p → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      (preparedResidualSolveCost
        (4*inverseExecutionExponent p l target
          (haloBoundary s t band a b).card band)
        (8*inverseExecutionExponent p l target
          (haloBoundary s t band a b).card band+8)
        (haloBoundary s t band a b).card (12*band+1) : ℝ) ≤
      C*((haloBoundaryCountBound s t band a b+1 : ℕ) : ℝ)*
        ((12*band+1 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := preparedResidual_selected_fast_le cl ct cG cG
  refine ⟨C,hC,?_⟩
  intro p l target s t band a b _ hp hst hband hl ht hgeometry
  let N := (haloBoundary s t band a b).card
  have hN : N ≤ s := by
    have hh := Finset.card_le_univ (haloBoundary s t band a b)
    rwa [ZMod.card] at hh
  have hNlog : Nat.size N ≤ cG*p := (Nat.size_le_size (hN.trans (by omega : s ≤ 2*s+1))).trans hgeometry
  have hBlog : Nat.size (2*band+1) ≤ cG*p := (Nat.size_le_size (by omega : 2*band+1 ≤ 2*s+1)).trans hgeometry
  have hh := hfast p l target N band hp hl ht hNlog hBlog
  have hrows : ((N+1 : ℕ) : ℝ) ≤
      ((haloBoundaryCountBound s t band a b+1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right
      (haloBoundary_card_bound hst band a b) 1
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrows hC) (Nat.cast_nonneg _)) (by positivity))

end IntegerMultBounds.MathlibTM2.Cost
