module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRetainedCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedPassGeometryCost

/-! The placed coupling pass uses one counter setup, fast active-row work and
linear source/page movement. Ordinary geometry controls stay explicit. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def retainedCouplingControlCost (P q s t u band a b : ℕ) : ℕ :=
  let w := 2*q+8
  installCouplingHeadersCost P q s t u band a b+closedCouplingSourceMaskCost s t band a b+
    (prepareCost q w+6*q+4*band+10)+(2*(w+q+Schoenhage.Schedule.topN w)+7)+
    releaseCouplingHeadersCost P q s t u band a b

theorem placedCachedCouplingGeometryCost_retained_le (P q s t u band a b : ℕ)
    (hs : 1 ≤ s) (hband : band ≤ s) :
    placedCachedCouplingGeometryCost P q s t u band a b ≤
      retainedCouplingControlCost P q s t u band a b+
        runRetainedPageCouplingRowsGeometryCost q (2*q+8) s t band a b+400*s*((2*q+8)+1) := by
  have hbw := Nat.mul_le_mul_right (2*q+8) hband
  dsimp only [placedCachedCouplingGeometryCost,retainedCouplingControlCost,
    runPreparedPageCouplingRowsGeometryCost,prepareSpatialCouplingSourceCost,prepareMaskedCouplingSourceCost,
    maskCouplingSourceCost,padCouplingSourceCost,retireSpatialCouplingSourceCost,retireCountedLineCost]
  nlinarith only [hs,hband,hbw,Nat.zero_le (s*(2*q+8))]

theorem placedCachedCouplingGeometry_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p P q s t u band a b : ℕ, ∀ [NeZero s],
      1 ≤ p → 2*q+8 ≤ cw*p → band ≤ s →
      let active := haloBoundaryCountBound s t (2*band) a b+4*band
      (placedCachedCouplingGeometryCost P q s t u band a b : ℝ) ≤
        (retainedCouplingControlCost P q s t u band a b : ℝ)+
          C*((s+active*(2*band+1) : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hrows⟩ := retainedCouplingRows_fast_le cw
  let D := 400*(cw+1)
  refine ⟨K+(D : ℝ),by positivity,?_⟩
  intro p P q s t u band a b _ hp hwidth hband
  dsimp only
  let volume := s+(haloBoundaryCountBound s t (2*band) a b+4*band)*(2*band+1)
  have hr := hrows p q (2*q+8) s t band a b hp (by omega) (NeZero.pos s) hwidth
  dsimp only at hr
  have hn := placedCachedCouplingGeometryCost_retained_le P q s t u band a b (NeZero.pos s) hband
  have hnR := (Nat.cast_le (α := ℝ)).mpr hn
  have hlinear : 400*s*((2*q+8)+1) ≤ D*(volume*p) := by
    have hv : s ≤ volume := by dsimp only [volume]; omega
    have hw : (2*q+8)+1 ≤ (cw+1)*p := by nlinarith only [hp,hwidth]
    have h := Nat.mul_le_mul hv hw
    dsimp only [D]
    nlinarith only [h]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hlinearR : ((400*s*((2*q+8)+1) : ℕ) : ℝ) ≤ (D : ℝ)*(volume : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
    calc
      _ ≤ (D : ℝ)*(volume : ℝ)*p := by exact_mod_cast (by simpa only [Nat.mul_assoc] using hlinear : 400*s*((2*q+8)+1) ≤ D*volume*p)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpPow (by positivity)
  push_cast at hnR
  dsimp only [volume] at hlinearR
  push_cast at hr hlinearR hnR ⊢
  nlinarith only [hnR,hr,hlinearR]

/-- Apply the bound to the actual placed cached pass, including its computed coefficient-page length. -/
theorem placedCachedRestoredCouplingPass_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p P q s t u band a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → 2*q+8 ≤ cw*p → band ≤ s → b ≤ s → ∀ boundary : Bool,
      let active := haloBoundaryCountBound s t (2*band) a b+4*band
      (placedCachedRestoredCouplingPassCost boundary P q s t u band a b
        (couplingCoefficientPage P q s t u band a b s).length : ℝ) ≤
      (retainedCouplingControlCost P q s t u band a b : ℝ)+
        C*((s+active*(2*band+1) : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := placedCachedCouplingGeometry_fast_le cw
  refine ⟨C,hC,?_⟩
  intro p P q s t u band a b _ hp hst hwidth hband hb boundary
  have h := hfast p P q s t u band a b hp hwidth hband
  have hcost := placedCachedRestoredCouplingPassCost_geometry_le hst boundary P q u band a b hb
  exact ((Nat.cast_le (α := ℝ)).mpr hcost).trans h

end IntegerMultBounds.MathlibTM2.Cost
