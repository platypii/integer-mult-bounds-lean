module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunPreparedPageCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPageCouplingCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunCachedPageCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageSize

/-! The page reader pays fast row arithmetic on active rows and linear copies on skipped rows. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem pageSpatialGuardedLoopCost_counts {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (q w band a b : ℕ) (hb : b ≤ s) :
    pageSpatialGuardedLoopCost boundary q w s t band a b s =
      (couplingZeroRows true s t band a b).card*(10*w+10)+
      (s-(couplingZeroRows true s t band a b).card)*consumePageSpatialCouplingRowCost q w band+
      s*(10*w+16)+2 := by
  let pred := fun i => couplingSkipAt boundary s t band a b i = true
  have hcount := Finset.card_filter_add_card_filter_not (s := Finset.range s) pred
  have htrue : ((Finset.range s).filter pred).card = (couplingZeroRows true s t band a b).card :=
    couplingGuard_true_count hst boundary band a b hb
  have hfalse : ((Finset.range s).filter (fun i => ¬pred i)).card =
      s-(couplingZeroRows true s t band a b).card := by
    rw [Finset.card_range,htrue] at hcount
    omega
  have heach (i : ℕ) : pageSpatialGuardedStepCost (couplingSkipAt boundary s t band a b i) q w band+3 =
      (if pred i then (10*w+10) else consumePageSpatialCouplingRowCost q w band)+(10*w+16) := by
    unfold pageSpatialGuardedStepCost guardedPageSpatialCouplingRowCost pred
    omega
  unfold pageSpatialGuardedLoopCost
  simp_rw [heach]
  rw [Finset.sum_add_distrib,Finset.sum_ite]
  simp [htrue,hfalse,smul_eq_mul,Nat.add_assoc]

theorem consumePageSpatialCouplingRowCost_eq (q w band : ℕ) :
    consumePageSpatialCouplingRowCost q w band =
      (2*band+1)*(rmulCost w+103*w+59)+prepareCost q w+32*w+8*q+8*band+
        2*Schoenhage.Schedule.topN w+156 := by
  unfold consumePageSpatialCouplingRowCost
  rw [pageSpatialCouplingRowCost_eq]
  unfold transferCountedLineCost
  ring

theorem pageSpatialGuardedLoopCost_le {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (q w band a b : ℕ) (hb : b ≤ s) :
    pageSpatialGuardedLoopCost boundary q w s t band a b s ≤
      s*(10*w+10)+(haloBoundaryCountBound s t (2*band) a b+4*band)*
        consumePageSpatialCouplingRowCost q w band+s*(10*w+16)+2 := by
  rw [pageSpatialGuardedLoopCost_counts hst boundary q w band a b hb]
  have hI : (couplingZeroRows true s t band a b).card ≤ s := by
    rw [← couplingGuard_true_count hst boundary band a b hb]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hz := Nat.mul_le_mul_right (10*w+10) hI
  have hf := Nat.mul_le_mul_right (consumePageSpatialCouplingRowCost q w band)
    (couplingGuard_full_count_le hst boundary band a b)
  omega

def runPreparedPageCouplingRowsGeometryCost (q w s t band a b : ℕ) : ℕ :=
  (prepareCost q w+6*q+4*band+10)+runRetainedPageCouplingRowsGeometryCost q w s t band a b+
    (2*(w+q+Schoenhage.Schedule.topN w)+7)

theorem runPreparedPageCouplingRowsCost_geometry_le {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (P q w u band a b : ℕ) (hb : b ≤ s) :
    runPreparedPageCouplingRowsCost boundary q w s t band a b
        (couplingCoefficientPage P q s t u band a b s).length ≤
      runPreparedPageCouplingRowsGeometryCost q w s t band a b := by
  exact runGeneratedRetainedPageCouplingRowsCost_geometry_le hst boundary P q w u band a b hb

theorem runCachedPageCouplingRowsCost_geometry_le {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (P q w u band a b : ℕ) (hb : b ≤ s) :
    runCachedPageCouplingRowsCost boundary q w s t band a b
        (couplingCoefficientPage P q s t u band a b s).length ≤
      10*s+10+runPreparedPageCouplingRowsGeometryCost q w s t band a b := by
  exact Nat.add_le_add_left (runPreparedPageCouplingRowsCost_geometry_le hst boundary P q w u band a b hb) _

/-- Retained guards, encoded coefficients, unary word count and row width; excludes execution scratch. -/
theorem couplingPageCache_owned_size_le_geometry {s t A : ℕ} [NeZero s] (hst : s < t)
    (P q w u band a b : ℕ) (hb : b ≤ s) :
    (couplingGuardSymbols true A s t band a b).length+
        (cstream A w (couplingCoefficientPage P q s t u band a b s)).length+
        (couplingCoefficientPage P q s t u band a b s).length+(2*band+1) ≤
      s+(haloBoundaryCountBound s t (2*band) a b+4*band)*(2*band+1)*(w+1)+(2*band+1) := by
  have h := couplingCoefficientPage_owned_size_le_geometry (A := A) hst P q w u band a b hb
  simp only [couplingGuardSymbols_length]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
