module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyBatchStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupKeys
public import IntegerMultBounds.MathlibTM2.StackCallResources

/-! A live repeated step needs one scratch allowance, independent of how many
replicas the batch contains. Its boundary stock is accounted for separately. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem familyComplexBatchStepCost_line_le (A p u l s t a b target : ℕ) [NeZero s] :
    familyComplexBatchStepCost A p u l s t a b target ≤
      generatedFamilyComplexLineCost A p u l s t a b target := by
  dsimp only [familyComplexBatchStepCost,generatedFamilyComplexLineCost]
  simp only [Nat.mul_assoc]
  omega

theorem selectedFamilyBatchStepCost_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ A u target a b : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      scale*familyComplexBatchStepCost A (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (Sizes.s n i) (Sizes.t n i) a b target ≤ Sizes.T n := by
  obtain ⟨C,hC,hline⟩ := selectedFamilyLine_fast_le ct
  filter_upwards [hline,selectedAxisPolynomial_le_volume (scale*⌈2*C⌉₊) 2 3] with n hl hv
  intro h i _ A u target a b hu htarget hband ha hb
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let band := PhaseCellBand.width p u
  let cost := familyComplexBatchStepCost A p u (haloInverseRingLog s t) s t a b target
  have hp : (1 : ℝ) ≤ p := by have := h.thirteen_le_p; dsimp [p]; norm_cast; omega
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp [t]; omega
  have hbs : band ≤ t := hband.trans (h.good.lt i).le
  have hgeom : t+(t-s)*band^2 ≤ 2*t^3 := by
    have hsq := Nat.pow_le_pow_left hbs 2
    have hg := Nat.mul_le_mul (Nat.sub_le t s) hsq
    have htpow : t ≤ t^3 := Nat.le_self_pow (by decide) t
    nlinarith only [hg,htpow]
  have hcost := (familyComplexBatchStepCost_line_le A p u (haloInverseRingLog s t) s t a b target).trans
    (generatedFamilyComplexLineCost_geometry_le (h.good.lt i) A p u (haloInverseRingLog s t) a b target hb)
  have hfast := hl h i u target a b hu htarget hband ha hb
  dsimp only at hfast
  have hcostR : (cost : ℝ) ≤ C*(t+(t-s)*band^2 : ℕ)*(p : ℝ)^(129/128 : ℝ) :=
    (by exact_mod_cast hcost : (cost : ℝ) ≤ _).trans hfast
  have hgeomR : ((t+(t-s)*band^2 : ℕ) : ℝ) ≤ 2*(t : ℝ)^3 := by exact_mod_cast hgeom
  have hpow : (p : ℝ)^(129/128 : ℝ) ≤ (p : ℝ)^2 := by
    have he := Real.rpow_le_rpow_of_exponent_le hp (show (129/128 : ℝ) ≤ 2 by norm_num)
    simpa only [Real.rpow_two] using he
  have hpoly : (cost : ℝ) ≤ (⌈2*C⌉₊ : ℝ)*(t : ℝ)^3*(p : ℝ)^2 := by
    calc
      _ ≤ C*(2*(t : ℝ)^3)*(p : ℝ)^2 := hcostR.trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hgeomR hC) hpow (by positivity) (by positivity))
      _ = (2*C)*(t : ℝ)^3*(p : ℝ)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Nat.le_ceil (2*C)) (by positivity)) (by positivity)
  have hnat : cost ≤ ⌈2*C⌉₊*t^3*p^2 := by exact_mod_cast hpoly
  exact (Nat.mul_le_mul_left scale hnat).trans (by convert hv i using 1 <;> ring)

theorem selectedFamilyBatchStep_trace_volume_le {Q A : ℕ} {P U : Type} [Fintype P]
    (body : P → Pr P 263 Q A U) (ct : ℕ) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ u target a b : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      ∀ (s t : Store (HΓ (T := 263) A) (HS 263 Q A U)) (steps depth : ℕ),
      steps ≤ familyComplexBatchStepCost A (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a b target →
      Exec body (familyComplexBatchStep recovery hR hQ) s steps t →
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+Sizes.T n)
        depth (familyComplexBatchStep recovery hR hQ) s steps t := by
  let c := max (mnProgPush (familyComplexBatchStep (P := P) (U := U) (A := A) recovery hR hQ))
    (mnPushC body)
  filter_upwards [selectedFamilyBatchStepCost_scaled_volume_le ct (c+1)] with n hn
  intro h i _ u target a b hu htarget hband ha hb s t steps depth hsteps he
  have hs := (Nat.mul_le_mul_left (c+1) hsteps).trans (hn h i A u target a b hu htarget hband ha hb)
  apply (mn_exec_finite_within he (budget := steps) (depth := depth) le_rfl).mono
  intro d z hz
  exact hz.trans (Nat.add_le_add_left hs _)

end IntegerMultBounds.MathlibTM2.Cost
