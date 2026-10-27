module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunGeneratedRetainedPageCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageSize

/-! The page reader pays fast row arithmetic on active rows and linear copies on skipped rows. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem retainedPageSpatialGuardedLoopCost_counts {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (q w band a b : ℕ) (hb : b ≤ s) :
    retainedPageSpatialGuardedLoopCost boundary q w s t band a b s =
      (couplingZeroRows true s t band a b).card*(10*w+10)+
      (s-(couplingZeroRows true s t band a b).card)*retainedConsumePageSpatialCouplingRowCost w band+
      s*(10*w+16)+2 := by
  let pred := fun i => couplingSkipAt boundary s t band a b i = true
  have hcount := Finset.card_filter_add_card_filter_not (s := Finset.range s) pred
  have htrue : ((Finset.range s).filter pred).card = (couplingZeroRows true s t band a b).card :=
    couplingGuard_true_count hst boundary band a b hb
  have hfalse : ((Finset.range s).filter (fun i => ¬pred i)).card =
      s-(couplingZeroRows true s t band a b).card := by
    rw [Finset.card_range,htrue] at hcount
    omega
  have heach (i : ℕ) : retainedPageSpatialGuardedStepCost (couplingSkipAt boundary s t band a b i) q w band+3 =
      (if pred i then (10*w+10) else retainedConsumePageSpatialCouplingRowCost w band)+(10*w+16) := by
    unfold retainedPageSpatialGuardedStepCost retainedGuardedPageSpatialCouplingRowCost pred
    omega
  unfold retainedPageSpatialGuardedLoopCost
  simp_rw [heach]
  rw [Finset.sum_add_distrib,Finset.sum_ite]
  simp [htrue,hfalse,smul_eq_mul,Nat.add_assoc]

theorem retainedConsumePageSpatialCouplingRowCost_eq (w band : ℕ) :
    retainedConsumePageSpatialCouplingRowCost w band =
      (2*band+1)*(rmulCost w+103*w+59)+30*w+4*band+139 := by
  unfold retainedConsumePageSpatialCouplingRowCost
  rw [retainedPageSpatialCouplingRowCost_eq]
  unfold transferCountedLineCost
  ring

theorem retainedPageSpatialGuardedLoopCost_le {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (q w band a b : ℕ) (hb : b ≤ s) :
    retainedPageSpatialGuardedLoopCost boundary q w s t band a b s ≤
      s*(10*w+10)+(haloBoundaryCountBound s t (2*band) a b+4*band)*
        retainedConsumePageSpatialCouplingRowCost w band+s*(10*w+16)+2 := by
  rw [retainedPageSpatialGuardedLoopCost_counts hst boundary q w band a b hb]
  have hI : (couplingZeroRows true s t band a b).card ≤ s := by
    rw [← couplingGuard_true_count hst boundary band a b hb]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hz := Nat.mul_le_mul_right (10*w+10) hI
  have hf := Nat.mul_le_mul_right (retainedConsumePageSpatialCouplingRowCost w band)
    (couplingGuard_full_count_le hst boundary band a b)
  omega

def runRetainedPageCouplingRowsGeometryCost (_q w s t band a b : ℕ) : ℕ :=
  let active := haloBoundaryCountBound s t (2*band) a b+4*band
  s*(10*w+10)+active*retainedConsumePageSpatialCouplingRowCost w band+s*(10*w+16)+2+
    32*s*w+34*s+28+transferCountedLineCost s w+transferCountedLineCost (active*(2*band+1)) w

theorem runRetainedPageCouplingRowsCost_geometry_le {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (P q w u band a b : ℕ) (hb : b ≤ s) :
    runRetainedPageCouplingRowsCost boundary q w s t band a b
        (couplingCoefficientPage P q s t u band a b s).length ≤
      runRetainedPageCouplingRowsGeometryCost q w s t band a b := by
  have hloop := retainedPageSpatialGuardedLoopCost_le hst boundary q w band a b hb
  have hwords := couplingCoefficientPage_length_le_geometry hst P q u band a b hb
  have hrestore := Nat.mul_le_mul_right (10*w+9) hwords
  dsimp only [runRetainedPageCouplingRowsCost,runRetainedPageCouplingRowsGeometryCost,transferCountedLineCost]
  omega

theorem runGeneratedRetainedPageCouplingRowsCost_geometry_le {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (P q w u band a b : ℕ) (hb : b ≤ s) :
    runGeneratedRetainedPageCouplingRowsCost boundary q w s t band a b
        (couplingCoefficientPage P q s t u band a b s).length ≤
      (prepareCost q w+6*q+4*band+10)+runRetainedPageCouplingRowsGeometryCost q w s t band a b+
        (2*(w+q+Schoenhage.Schedule.topN w)+7) := by
  dsimp only [runGeneratedRetainedPageCouplingRowsCost]
  have h := runRetainedPageCouplingRowsCost_geometry_le hst boundary P q w u band a b hb
  omega

/-- All row arithmetic and page traversal is linear in the row's coefficient count. -/
theorem retainedConsumePageSpatialCouplingRowCost_le (w band : ℕ) :
    retainedConsumePageSpatialCouplingRowCost w band ≤ 400*(2*band+1)*(rmulCost w+w+1) := by
  rw [retainedConsumePageSpatialCouplingRowCost_eq]
  have hw : w ≤ (2*band+1)*w := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith only [hw,Nat.zero_le ((2*band+1)*rmulCost w),Nat.zero_le band]

theorem runRetainedPageCouplingRowsGeometryCost_le (q w s t band a b : ℕ) (hs : 1 ≤ s) :
    let active := haloBoundaryCountBound s t (2*band) a b+4*band
    runRetainedPageCouplingRowsGeometryCost q w s t band a b ≤
      1000*(s+active*(2*band+1))*(rmulCost w+w+1) := by
  dsimp only
  let active := haloBoundaryCountBound s t (2*band) a b+4*band
  have hrow := Nat.mul_le_mul_left active (retainedConsumePageSpatialCouplingRowCost_le w band)
  dsimp only [runRetainedPageCouplingRowsGeometryCost,transferCountedLineCost]
  change s*(10*w+10)+active*retainedConsumePageSpatialCouplingRowCost w band+s*(10*w+16)+2+
    32*s*w+34*s+28+(s*(10*w+9)+10)+(active*(2*band+1)*(10*w+9)+10) ≤
      1000*(s+active*(2*band+1))*(rmulCost w+w+1)
  nlinarith only [hrow,hs,Nat.zero_le (s*rmulCost w),Nat.zero_le (s*w),
    Nat.zero_le (active*(2*band+1)*rmulCost w),Nat.zero_le (active*(2*band+1)*w),
    Nat.zero_le (active*(2*band+1))]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
