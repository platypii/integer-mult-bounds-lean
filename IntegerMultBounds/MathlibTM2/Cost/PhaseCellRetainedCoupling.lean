module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPageCouplingCost
public import IntegerMultBounds.MathlibTM2.Cost.ChirpLogGrowth

/-! Fast active-row arithmetic and page traversal with one separately paid
counter construction and release per complete coupling pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem retainedCouplingRows_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q w s t band a b : ℕ, 1 ≤ p → 1 ≤ w → 1 ≤ s → w ≤ cw*p →
      let active := haloBoundaryCountBound s t (2*band) a b+4*band
      (runRetainedPageCouplingRowsGeometryCost q w s t band a b : ℝ) ≤
        C*((s+active*(2*band+1) : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hmul⟩ := chirp_rmul_le cw
  refine ⟨1000*(K+(cw : ℝ)+1),by positivity,?_⟩
  intro p q w s t band a b hp hw hs hwidth
  dsimp only
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hOne : (1 : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
  have hwR : (w : ℝ) ≤ (cw : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
    calc
      _ ≤ (cw : ℝ)*p := by exact_mod_cast hwidth
      _ ≤ _ := mul_le_mul_of_nonneg_left hpPow (Nat.cast_nonneg cw)
  have hscalar : ((rmulCost w+w+1 : ℕ) : ℝ) ≤ (K+(cw : ℝ)+1)*(p : ℝ)^(129/128 : ℝ) := by
    push_cast
    have h := hmul p w hp hw hwidth
    nlinarith only [h,hwR,hOne]
  let volume := s+(haloBoundaryCountBound s t (2*band) a b+4*band)*(2*band+1)
  calc
    _ ≤ 1000*(volume : ℝ)*((rmulCost w+w+1 : ℕ) : ℝ) := by
      exact_mod_cast runRetainedPageCouplingRowsGeometryCost_le q w s t band a b hs
    _ ≤ 1000*(volume : ℝ)*((K+(cw : ℝ)+1)*(p : ℝ)^(129/128 : ℝ)) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = _ := by ring

/-- The full generated pass retains a single counter setup/release charge outside its row volume. -/
theorem generatedRetainedCouplingRows_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p P q w s t u band a b : ℕ, ∀ [NeZero s],
      1 ≤ p → 1 ≤ w → s < t → w ≤ cw*p → b ≤ s → ∀ boundary : Bool,
      let active := haloBoundaryCountBound s t (2*band) a b+4*band
      (runGeneratedRetainedPageCouplingRowsCost boundary q w s t band a b
        (couplingCoefficientPage P q s t u band a b s).length : ℝ) ≤
      ((prepareCost q w+6*q+4*band+10+(2*(w+q+Schoenhage.Schedule.topN w)+7) : ℕ) : ℝ)+
        C*((s+active*(2*band+1) : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := retainedCouplingRows_fast_le cw
  refine ⟨C,hC,?_⟩
  intro p P q w s t u band a b _ hp hw hst hwidth hb boundary
  have h := hfast p q w s t band a b hp hw (NeZero.pos s) hwidth
  have hcost := runGeneratedRetainedPageCouplingRowsCost_geometry_le hst boundary P q w u band a b hb
  have hcostR := (Nat.cast_le (α := ℝ)).mpr hcost
  dsimp only at h
  push_cast at h hcostR ⊢
  linarith only [h,hcostR]

end IntegerMultBounds.MathlibTM2.Cost
