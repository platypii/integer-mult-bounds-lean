module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedRetainedCouplingCost
public import IntegerMultBounds.MathlibTM2.Cost.ChirpLogGrowth

/-! Retained coupling pays one fast multiplication stream per active spatial row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem retainedPageSpatialGuardedStepCost_le (skip : Bool) (q w band : ℕ) :
    retainedPageSpatialGuardedStepCost skip q w band ≤
      1000*(band+1)*(rmulCost w+w+1) := by
  cases skip <;>
    simp only [retainedPageSpatialGuardedStepCost,retainedGuardedPageSpatialCouplingRowCost,
      Bool.false_eq_true,ite_false,ite_true,retainedConsumePageSpatialCouplingRowCost,
      retainedPageSpatialCouplingRowCost,prepareCountedCouplingInputsCost,
      copyCountedLineCost,transferCountedLineCost,retainedCouplingRowCost]
  all_goals nlinarith only [Nat.zero_le (band*rmulCost w),Nat.zero_le (band*w),
    Nat.zero_le (rmulCost w),Nat.zero_le w,Nat.zero_le band]

theorem retainedPageSpatialIntervalLoopCost_le (boundary : Bool) (q w s t band a b origin N : ℕ) :
    retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N ≤
      N*(1000*(band+1)*(rmulCost w+w+1)+3)+2 := by
  unfold retainedPageSpatialIntervalLoopCost
  apply Nat.add_le_add_right
  calc
    _ ≤ (Finset.range N).sum (fun _ => 1000*(band+1)*(rmulCost w+w+1)+3) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.add_le_add_right (retainedPageSpatialGuardedStepCost_le _ q w band) 3
    _ = _ := by simp

def retainedCouplingActiveRows (boundary : Bool) (s t band a b origin N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun j => couplingSkipAt boundary s t band a b (origin+j) = false)).card

theorem retainedPageSpatialGuardedStepCost_mask_le (skip : Bool) (q w band : ℕ) :
    retainedPageSpatialGuardedStepCost skip q w band ≤ 20*w+23+
      (if skip = false then 1000*(band+1)*(rmulCost w+w+1) else 0) := by
  cases skip with
  | false =>
    have h := retainedPageSpatialGuardedStepCost_le false q w band
    simp only [ite_true]
    exact h.trans (Nat.le_add_left _ _)
  | true =>
    simp [retainedPageSpatialGuardedStepCost,retainedGuardedPageSpatialCouplingRowCost]
    omega

theorem retainedPageSpatialIntervalLoopCost_mask_le (boundary : Bool) (q w s t band a b origin N : ℕ) :
    retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N ≤
      N*(20*w+26)+retainedCouplingActiveRows boundary s t band a b origin N*
        (1000*(band+1)*(rmulCost w+w+1))+2 := by
  unfold retainedPageSpatialIntervalLoopCost
  apply Nat.add_le_add_right
  calc
    _ ≤ (Finset.range N).sum (fun j => (20*w+26)+
        (if couplingSkipAt boundary s t band a b (origin+j) = false then
          1000*(band+1)*(rmulCost w+w+1) else 0)) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := retainedPageSpatialGuardedStepCost_mask_le
        (couplingSkipAt boundary s t band a b (origin+j)) q w band
      omega
    _ = _ := by simp [Finset.sum_add_distrib,←Finset.sum_filter,retainedCouplingActiveRows]

theorem retainedPageSpatialIntervalLoopCost_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p q w s t band a b origin N : ℕ) (boundary : Bool),
      1 ≤ p → 1 ≤ w → w ≤ cw*p →
      (retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N : ℝ) ≤
        N*(C*((band+1 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ)+3)+2 := by
  obtain ⟨K,hK,hproduct⟩ := chirp_rmul_le cw
  refine ⟨1000*(K+(cw : ℝ)+1),by positivity,?_⟩
  intro p q w s t band a b origin N boundary hp hw hwidth
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hone : (1 : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
  have hwidthR : (w : ℝ) ≤ (cw : ℝ)*(p : ℝ) := by exact_mod_cast hwidth
  have hwPow := hwidthR.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg cw))
  have hscalar : ((rmulCost w+w+1 : ℕ) : ℝ) ≤ (K+(cw : ℝ)+1)*(p : ℝ)^(129/128 : ℝ) := by
    push_cast
    have hh := add_le_add (add_le_add (hproduct p w hp hw hwidth) hwPow) hone
    nlinarith only [hh]
  have hloop : (retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N : ℝ) ≤
      N*(1000*((band+1 : ℕ) : ℝ)*((rmulCost w+w+1 : ℕ) : ℝ)+3)+2 := by
    exact_mod_cast retainedPageSpatialIntervalLoopCost_le boundary q w s t band a b origin N
  have hs := mul_le_mul_of_nonneg_left hscalar (by positivity : (0 : ℝ) ≤ (N : ℝ)*1000*(band+1))
  push_cast at hloop hs ⊢
  nlinarith only [hloop,hs]

theorem retainedPageSpatialIntervalLoopCost_mask_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p q w s t band a b origin N : ℕ) (boundary : Bool),
      1 ≤ p → 1 ≤ w → w ≤ cw*p →
      (retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N : ℝ) ≤
        N*(20*w+26)+2+C*(retainedCouplingActiveRows boundary s t band a b origin N)*((band+1 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hproduct⟩ := chirp_rmul_le cw
  refine ⟨1000*(K+(cw : ℝ)+1),by positivity,?_⟩
  intro p q w s t band a b origin N boundary hp hw hwidth
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hone : (1 : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
  have hwidthR : (w : ℝ) ≤ (cw : ℝ)*(p : ℝ) := by exact_mod_cast hwidth
  have hwPow := hwidthR.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg cw))
  have hscalar : ((rmulCost w+w+1 : ℕ) : ℝ) ≤ (K+(cw : ℝ)+1)*(p : ℝ)^(129/128 : ℝ) := by
    push_cast
    have hh := add_le_add (add_le_add (hproduct p w hp hw hwidth) hwPow) hone
    nlinarith only [hh]
  have hloop : (retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N : ℝ) ≤
      N*(20*w+26)+(retainedCouplingActiveRows boundary s t band a b origin N)*(1000*((band+1 : ℕ) : ℝ)*((rmulCost w+w+1 : ℕ) : ℝ))+2 := by
    exact_mod_cast retainedPageSpatialIntervalLoopCost_mask_le boundary q w s t band a b origin N
  have hs := mul_le_mul_of_nonneg_left hscalar (by positivity : (0 : ℝ) ≤ (retainedCouplingActiveRows boundary s t band a b origin N : ℝ)*1000*(band+1))
  push_cast at hloop hs ⊢
  nlinarith only [hloop,hs]

noncomputable def retainedCouplingIntervalNativeCost (boundary : Bool)
    (P q w s t u band a b origin N V : ℕ) : ℕ :=
  preparedSharedLocalFeedCouplingIntervalCost boundary P q w s t u band a b origin N V-
    retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N

theorem preparedSharedLocalFeedCouplingIntervalCost_split (boundary : Bool)
    (P q w s t u band a b origin N V : ℕ) :
    preparedSharedLocalFeedCouplingIntervalCost boundary P q w s t u band a b origin N V =
      retainedCouplingIntervalNativeCost boundary P q w s t u band a b origin N V+
        retainedPageSpatialIntervalLoopCost boundary q w s t band a b origin N := by
  unfold retainedCouplingIntervalNativeCost
  apply (Nat.sub_add_cancel ?_).symm
  unfold preparedSharedLocalFeedCouplingIntervalCost
  omega

theorem preparedSharedLocalFeedCouplingIntervalCost_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p P q w s t u band a b origin N V : ℕ) (boundary : Bool),
      1 ≤ p → 1 ≤ w → w ≤ cw*p →
      (preparedSharedLocalFeedCouplingIntervalCost boundary P q w s t u band a b origin N V : ℝ) ≤
        retainedCouplingIntervalNativeCost boundary P q w s t u band a b origin N V+
          N*(C*((band+1 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ)+3)+2 := by
  obtain ⟨C,hC,hfast⟩ := retainedPageSpatialIntervalLoopCost_fast_le cw
  refine ⟨C,hC,?_⟩
  intro p P q w s t u band a b origin N V boundary hp hw hwidth
  have hh := hfast p q w s t band a b origin N boundary hp hw hwidth
  rw [preparedSharedLocalFeedCouplingIntervalCost_split]
  push_cast at hh ⊢
  linarith only [hh]

end IntegerMultBounds.MathlibTM2.Cost
