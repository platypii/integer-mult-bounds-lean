module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedPreparedCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedEnvelope
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCouplingSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! The actual prepared packed solver has a polynomial scratch bill at selected
parameters. Its initial and recovery arithmetic reuse the existing pair estimate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedPackedPreparedInputCost_poly_le (ct cv : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b V : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n → a ≤ b → b ≤ Sizes.s n i →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → V ≤ cv*Sizes.p n →
      packedHaloPreparedInputCost (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (target+1) 2 (Sizes.s n i) (Sizes.t n i) a b V ≤ C*Sizes.t n i^5*Sizes.p n^4 := by
  obtain ⟨D,hD,hpair⟩ := selectedInteriorPair_fast_le ct
  let cw := 1032+8*ct
  let cZ := 2^15+2*cw+cv+426100
  let K := 50000000*(ssMulConst+1)*cZ^4
  refine ⟨⌈D⌉₊+K,?_⟩
  filter_upwards [hpair] with n hn
  intro h i _ u target a b V hu htarget hab hb hband hV
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let boundaryTarget := boundaryRecoveryTarget p (target+1)
  let bits := boundaryTableBits p boundaryTarget 2 N
  let stage := initialSchurTarget p u bits 2
  let e := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  let Z := cZ*t*p
  let G₁ := familyHaloInteriorGeometryCost p l s t u stage 2 a b
  let G₂ := familyHaloInteriorGeometryCost p l s t u (recoveryTarget p bits) e a b
  let cost := packedHaloPreparedInputCost p u l (target+1) 2 s t a b V
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hst : s < t := h.good.lt i
  have henv := selectedPackedPreparedPassEnvelopes ct cv h i u target a b V hu htarget hab hb hband hV
  have hw := selectedInverseWorkingWidth_le ct h i u target a b htarget hband
  have hqw : q ≤ w := by dsimp only [q,w,executionPrecision,executionWidth]; omega
  have hlift := selectedLiftedCoefficientWidth_le cw h i q w u band hw hqw hu hband
  have hcoefficient : 2*cw+426064 ≤ cZ*t :=
    (show 2*cw+426064 ≤ cZ by dsimp only [cZ]; omega).trans (Nat.le_mul_of_pos_right cZ ht)
  have hliftZ : liftedCoefficientWidth (2^15*p) q w s t u band ≤ Z :=
    hlift.trans (Nat.mul_le_mul_right p hcoefficient)
  have hprice := packedHaloPreparedInputCost_weights_poly hst p u l (target+1) a b V Z
    (hab.trans hb) hb henv.1 henv.2 hliftZ
  have hk : boundaryHaloRecoveryTarget p boundaryTarget N = recoveryTarget p bits := by
    dsimp only [bits,boundaryHaloRecoveryTarget,recoveryTarget,recoveryGuardBits,boundaryTableBits,boundaryErrorBits]
    omega
  rw [hk] at hprice
  change cost ≤ G₁+G₂+50000000*(ssMulConst+1)*t*Z^4 at hprice
  have hpoly : 50000000*(ssMulConst+1)*t*Z^4 = K*t^5*p^4 := by dsimp only [Z,K]; ring
  rw [hpoly] at hprice
  have hcostR : (cost : ℝ) ≤ (G₁ : ℝ)+(G₂ : ℝ)+(K : ℝ)*(t : ℝ)^5*(p : ℝ)^4 := by exact_mod_cast hprice
  have hpairR := hn h i u target a b hu htarget hband (hab.trans hb) hb
  change (G₁ : ℝ)+(G₂ : ℝ) ≤ D*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) at hpairR
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpowP : (p : ℝ)^(129/128 : ℝ) ≤ (p : ℝ)^4 := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hpR (show (129/128 : ℝ) ≤ (4 : ℕ) by norm_num)
  have hpowT : (t : ℝ) ≤ (t : ℝ)^5 := by exact_mod_cast (Nat.le_self_pow (by decide : 5 ≠ 0) t)
  have hpairPoly : (G₁ : ℝ)+(G₂ : ℝ) ≤ (⌈D⌉₊ : ℝ)*(t : ℝ)^5*(p : ℝ)^4 := by
    calc
      _ ≤ D*(t : ℝ)^5*(p : ℝ)^4 := hpairR.trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hpowT hD) hpowP (by positivity) (by positivity))
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Nat.le_ceil D) (by positivity)) (by positivity)
  have hfinal : (cost : ℝ) ≤ ((⌈D⌉₊+K : ℕ) : ℝ)*(t : ℝ)^5*(p : ℝ)^4 := by
    push_cast
    nlinarith only [hcostR,hpairPoly]
  exact_mod_cast hfinal

/-- One numerical scratch bank fits the selected global volume, independently
of how many input replicas reuse the factors. -/
theorem selectedPackedPreparedInputCost_scaled_volume_le (ct cv scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b V : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n → a ≤ b → b ≤ Sizes.s n i →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → V ≤ cv*Sizes.p n →
      scale*packedHaloPreparedInputCost (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (target+1) 2 (Sizes.s n i) (Sizes.t n i) a b V ≤ Sizes.T n := by
  obtain ⟨C,hcost⟩ := selectedPackedPreparedInputCost_poly_le ct cv
  filter_upwards [hcost,selectedAxisPolynomial_le_volume (scale*C) 4 5] with n hc hv
  intro h i _ u target a b V hu ht hab hb hband hV
  exact (Nat.mul_le_mul_left scale (hc h i u target a b V hu ht hab hb hband hV)).trans
    (by convert hv i using 1 <;> ring)

end IntegerMultBounds.MathlibTM2.Cost
