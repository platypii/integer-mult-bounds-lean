module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicTransposeSplitPlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicTransposeWiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Width-sensitive accounting for exact rectangular routing. Full-width
stages retain their sublinear interchange charge; residual stages are paid
by their own widths, not by the largest field in the original rectangle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

noncomputable def DyadicTransposePlan.weightedCharge (f : ℕ → ℝ) {a b W : ℕ} :
    DyadicTransposePlan a b W → ℝ
  | .zeroLeft _ _ => 0
  | .zeroRight _ _ => 0
  | .left (b := b) _ rest => f b+rest.weightedCharge f
  | .right (a := a) _ rest => f a+rest.weightedCharge f

@[simp] theorem DyadicTransposePlan.weightedCharge_cast {a a' b W : ℕ}
    (h : a = a') (plan : DyadicTransposePlan a b W) (f : ℕ → ℝ) :
    (h ▸ plan).weightedCharge f = plan.weightedCharge f := by
  subst a'
  rfl

theorem DyadicTransposePlan.weightedCharge_eq {a b W : ℕ}
    (plan : DyadicTransposePlan a b W) (f : ℕ → ℝ) :
    (plan.stages.map (fun r => f (Nat.log 2 r.leftWidth))).sum = plan.weightedCharge f := by
  induction plan with
  | zeroLeft => rfl
  | zeroRight => rfl
  | left hb rest ih =>
    simp only [DyadicTransposePlan.stages,List.map_cons,List.sum_cons,
      Nat.log_pow (by decide : 1 < 2),weightedCharge,ih]
  | right ha rest ih =>
    have he : ((rest.stages.reverse.map RectangularChunkSwap.inverse).map
        (fun r => f (Nat.log 2 r.leftWidth))).sum =
        (rest.stages.map (fun r => f (Nat.log 2 r.leftWidth))).sum := by
      rw [List.map_map]
      dsimp only [Function.comp_def]
      have hm : rest.stages.reverse.map (fun r => f (Nat.log 2 r.inverse.leftWidth)) =
          rest.stages.reverse.map (fun r => f (Nat.log 2 r.leftWidth)) := by
        apply List.map_congr_left
        intro r hr
        dsimp only [RectangularChunkSwap.inverse]
        rw [rest.stages_equalWidth r (List.mem_reverse.mp hr)]
      rw [hm,List.map_reverse,List.sum_reverse]
    simp only [DyadicTransposePlan.stages,List.map_append,List.sum_append,he,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      Nat.log_pow (by decide : 1 < 2),weightedCharge,ih]
    exact add_comm _ _

theorem DyadicTransposePlan.wiredStages_weightedCharge_eq {a b W T : ℕ}
    (plan : DyadicTransposePlan a b W) (dims : RectangularChunkSwap → Fin 5 → Fin T)
    (f : ℕ → ℝ) :
    ((plan.wiredStages dims).map (fun r => f r.leftBits)).sum = plan.weightedCharge f := by
  simpa only [DyadicTransposePlan.wiredStages,List.map_map,Function.comp_def] using
    plan.weightedCharge_eq f

theorem DyadicTransposePlan.weightedCharge_le_linear {a b W : ℕ}
    (plan : DyadicTransposePlan a b W) (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k : ℕ, 0 < k → f k ≤ C*k) :
    plan.weightedCharge f ≤ C*(a+b : ℕ) := by
  induction plan with
  | zeroLeft => simp only [weightedCharge]; positivity
  | zeroRight => simp only [weightedCharge]; positivity
  | @left a b W hb rest ih =>
    have hh := hf b hb
    simp only [weightedCharge]
    push_cast at ih ⊢
    nlinarith only [ih,hh]
  | @right a b W ha rest ih =>
    have hh := hf a ha
    simp only [weightedCharge]
    push_cast at ih ⊢
    nlinarith only [ih,hh]

theorem dyadicTransposeSplitPlan_weightedCharge_le (q r b W : ℕ) (hb : 0 < b)
    (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k : ℕ, 0 < k → f k ≤ C*k) :
    (dyadicTransposeSplitPlan q r b W hb).weightedCharge f ≤
      q*f b+C*(r+b : ℕ) := by
  induction q generalizing W with
  | zero =>
    simpa only [dyadicTransposeSplitPlan,DyadicTransposePlan.weightedCharge_cast,Nat.cast_zero,zero_mul,zero_add] using
      (dyadicTransposePlan (r+b) r b W (by omega)).weightedCharge_le_linear f C hC hf
  | succ q ih =>
    have hh := ih (2^b*W)
    simpa only [dyadicTransposeSplitPlan,DyadicTransposePlan.weightedCharge_cast,DyadicTransposePlan.weightedCharge,
      Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_assoc,add_comm,add_left_comm] using
      add_le_add_left hh (f b)

/-- The residual route costs at most twice its exponent volume for every
sublinear width exponent. Full-width stages keep the sharper `b^τ` term. -/
theorem dyadicTransposeSplitPlan_rpowCharge_le (q r b W : ℕ) (hb : 0 < b)
    (τ : ℝ) (hτ : τ ≤ 1) :
    (dyadicTransposeSplitPlan q r b W hb).weightedCharge (fun k => (k : ℝ)^τ+1) ≤
      q*((b : ℝ)^τ+1)+2*(r+b : ℕ) := by
  apply dyadicTransposeSplitPlan_weightedCharge_le q r b W hb _ 2 (by norm_num)
  intro k hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hh := Real.rpow_le_rpow_of_exponent_le hkR hτ
  rw [Real.rpow_one] at hh
  linarith

theorem dyadicTransposeExactPlan_rpowCharge_le (a b W : ℕ) (hb : 0 < b)
    (τ : ℝ) (hτ : τ ≤ 1) :
    (dyadicTransposeExactPlan a b W hb).weightedCharge (fun k => (k : ℝ)^τ+1) ≤
      (a : ℝ)/b*((b : ℝ)^τ+1)+4*b := by
  have hh := dyadicTransposeSplitPlan_rpowCharge_le (a/b) (a%b) b W hb τ hτ
  have hrem : a%b ≤ b := (Nat.mod_lt a hb).le
  have hq : ((a/b : ℕ) : ℝ) ≤ (a : ℝ)/b := by
    apply (le_div_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)).2
    exact_mod_cast Nat.div_mul_le_self a b
  have hp : 0 ≤ (b : ℝ)^τ+1 := by positivity
  have hm := mul_le_mul_of_nonneg_right hq hp
  have hr : ((a%b : ℕ) : ℝ) ≤ b := by exact_mod_cast hrem
  simp only [dyadicTransposeExactPlan,DyadicTransposePlan.weightedCharge_cast]
  push_cast at hh
  linarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
