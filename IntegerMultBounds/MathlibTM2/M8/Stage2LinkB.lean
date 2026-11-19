module

public import IntegerMultBounds.MathlibTM2.M8.Global.HistogramB
public import IntegerMultBounds.MathlibTM2.M8.Stage2Link
public import IntegerMultBounds.MathlibTM2.M8.Stage2MomentsB

/-! The actual gauged design-B node satisfies the checked stopped-recurrence moment premises. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Moments
noncomputable section
open IntegerMultBounds.MathlibTM2.M8.Frames IntegerMultBounds.MathlibTM2.M8.Local
open Global.DesignB
open Global.Branching97 (roleCount)

/-- The checked histogram bounds the full executed node, including all owned work. -/
theorem edgeMomentB_le_histogram (φ : Nat → ℝ) (hnn : ∀ r, 0 ≤ φ r) (hmono : Monotone φ)
    (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b) :
    Global.edgeMoment φ Global.DesignB.framedNode ≤ histMoment φ histogramB := by
  have h := node_moment_le_signed_chains φ hnn hmono hsub
  rw [Finset.sum_add_distrib, sum_source_chainMoment, sum_target_chainMoment,
    sum_auxiliary_chainMoment, sum_exterior_moment] at h
  have he : 2 * 1771 * (Global.evalH φ SignedHistogramB.sourceHist + Global.evalH φ SignedHistogramB.targetHist +
      (Global.evalH φ SignedHistogramB.auxHist + Global.evalH (fun r => φ (506 + r)) SignedHistogramB.sigmaHist) +
      23 * φ 22) + (1771 : ℝ)^2 * (2 * φ 484 + φ 1) = histMoment φ histogramB := by
    simp only [Global.evalH, Finset.sum_range_succ, Finset.sum_range_zero,
      SignedHistogramB.sourceHist, SignedHistogramB.targetHist, SignedHistogramB.auxHist, SignedHistogramB.sigmaHist,
      List.getD_cons_zero, List.getD_cons_succ, histMoment, histogramB,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    norm_num [Global.wt]
    ring
  exact h.trans_eq he

/-- The moment of the physical node at any stopped exponent between zero and one. -/
theorem edgeMomentB_rpow_le {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    Global.edgeMoment (fun r => ((r : ℝ) / 529)^τ / roleCount) Global.DesignB.framedNode ≤
      moment τ histogramB := by
  rw [← histMoment_rpow]
  refine edgeMomentB_le_histogram _ (fun r => by positivity) (fun a b hab => ?_)
    (rpow_sub_add hτ0.le hτ1)
  refine div_le_div_of_nonneg_right ?_ (by norm_num [roleCount])
  exact Real.rpow_le_rpow (by positivity)
    (div_le_div_of_nonneg_right (by exact_mod_cast hab) (by norm_num)) hτ0.le

/-- The linear contraction is unchanged by the new frames. -/
theorem linear_premiseB :
    Global.edgeMoment (fun r => ((r : ℝ) / 529)^(1 : ℝ) / roleCount) Global.DesignB.framedNode ≤ q₁ := by
  have h := edgeMomentB_rpow_le (τ := 1) one_pos le_rfl
  rw [linear_momentB] at h
  exact_mod_cast h

/-- The actual node has the design-B stopped moment gap at saving `12402/10^8`. -/
theorem tau_premiseB :
    Global.edgeMoment (fun r => ((r : ℝ) / 529)^(1 - (savingB : ℝ)) / roleCount)
      Global.DesignB.framedNode < qτB := by
  have hs : (savingB : ℝ) = 12402 / 10^8 := by norm_num [savingB]
  have h := edgeMomentB_rpow_le (τ := 1 - (savingB : ℝ)) (by rw [hs]; norm_num) (by rw [hs]; norm_num)
  exact h.trans_lt tau_momentB

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Moments
