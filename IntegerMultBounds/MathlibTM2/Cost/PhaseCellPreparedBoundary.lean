module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInversePrecisionSetup
public import IntegerMultBounds.MathlibTM2.Cost.ChirpLogGrowth

/-! Fast repeated boundary solves at the inverse caller's selected precision, with setup charged separately. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- The selected inverse width is linear when the target, ring logarithm and geometry bit counts are linear. -/
theorem inverseExecutionWidth_le (p l target N band cl ct cN cB : ℕ) (hp : 1 ≤ p)
    (hl : l ≤ cl*p) (ht : target ≤ ct*p) (hN : Nat.size N ≤ cN*p)
    (hB : Nat.size (2*band+1) ≤ cB*p) :
    8*inverseExecutionExponent p l target N band+8 ≤
      (16*cl+8*ct+8*cN+8*cB+680)*p := by
  have hlog : Nat.size (8*p) ≤ 8*p := Nat.size_le.mpr Nat.lt_two_pow_self
  dsimp [inverseExecutionExponent]
  nlinarith only [hp,hl,ht,hN,hB,hlog]

/-- Factor setup is absent from this repeated solve allowance; the actual prepared kernel pays rows times bandwidth. -/
theorem preparedBoundary_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p w N W : ℕ, 1 ≤ p → 1 ≤ w → w ≤ cw*p → 1 ≤ W →
      (preparedBoundarySolveCost w N W : ℝ) ≤ C*((N+1 : ℕ) : ℝ)*(W : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hproduct⟩ := chirp_rmul_le cw
  refine ⟨400*(K+(cw : ℝ)+1),by positivity,?_⟩
  intro p w N W hp hw hwidth hW
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
  have hkernel : (preparedBoundarySolveCost w N W : ℝ) ≤
      400*((N+1 : ℕ) : ℝ)*(W : ℝ)*((rmulCost w+w+1 : ℕ) : ℝ) := by
    exact_mod_cast preparedBoundarySolveCost_le w N W hW
  calc
    _ ≤ 400*((N+1 : ℕ) : ℝ)*(W : ℝ)*((K+(cw : ℝ)+1)*(p : ℝ)^(129/128 : ℝ)) :=
      hkernel.trans (mul_le_mul_of_nonneg_left hscalar (by positivity))
    _ = _ := by ring

/-- Apply the repeated-kernel bound to the actual precision formula, rather than a separately supplied working width. -/
theorem preparedBoundary_selected_fast_le (cl ct cN cB : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p l target N band : ℕ, 1 ≤ p →
      l ≤ cl*p → target ≤ ct*p → Nat.size N ≤ cN*p → Nat.size (2*band+1) ≤ cB*p →
      (preparedBoundarySolveCost (8*inverseExecutionExponent p l target N band+8) N (12*band+1) : ℝ) ≤
        C*((N+1 : ℕ) : ℝ)*((12*band+1 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := preparedBoundary_fast_le (16*cl+8*ct+8*cN+8*cB+680)
  refine ⟨C,hC,?_⟩
  intro p l target N band hp hl ht hN hB
  exact hfast p _ N (12*band+1) hp (by omega)
    (inverseExecutionWidth_le p l target N band cl ct cN cB hp hl ht hN hB) (by omega)

/-- Ambient geometry bounds both precision bit counts and the actual boundary row work. -/
theorem preparedHaloBoundary_selected_fast_le (cl ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p l target s t band a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → band ≤ s → l ≤ cl*p → target ≤ ct*p → Nat.size (2*s+1) ≤ cG*p →
      (preparedBoundarySolveCost
        (8*inverseExecutionExponent p l target
          (haloBoundary s t band a b).card band+8)
        (haloBoundary s t band a b).card (12*band+1) : ℝ) ≤
      C*((haloBoundaryCountBound s t band a b+1 : ℕ) : ℝ)*
        ((12*band+1 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := preparedBoundary_selected_fast_le cl ct cG cG
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
