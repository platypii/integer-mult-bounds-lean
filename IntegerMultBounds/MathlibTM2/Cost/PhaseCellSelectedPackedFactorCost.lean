module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedFactorCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorConstruction
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! The actual packed factor construction and disposal reuse the established
selected family setup estimate, with polynomial control work added once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedConstructedBoundaryFactorCost_poly_le (ct : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      constructedBoundaryFactorCost (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (Sizes.s n i) (Sizes.t n i) a b (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2 ≤
        C*Sizes.t n i^6*Sizes.p n^4 := by
  obtain ⟨D,hD,hsetup⟩ := selectedFamilySetup_poly_le ct
  refine ⟨⌈D⌉₊,?_⟩
  filter_upwards [hsetup] with n hn
  intro h i _ u target a b hu ht hband ha hb
  have hfactor := constructedBoundaryFactorCost_le (Sizes.p n) u
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a b
    (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2
  have hsource : constructedBoundaryFactorCostBound (Sizes.p n) u
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a b
      (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2 ≤
      generatedFamilyComplexSetupCostBound 0 (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a b target := by
    dsimp only [generatedFamilyComplexSetupCostBound,generatedComplexSetupCostBound]
    omega
  have hselected := hn h i 0 u target a b hu ht hband ha hb
  have hcostR := (show (constructedBoundaryFactorCost (Sizes.p n) u
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a b
      (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2 : ℝ) ≤
      generatedFamilyComplexSetupCostBound 0 (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a b target by
    exact_mod_cast hfactor.trans hsource).trans hselected
  have hscale := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.le_ceil D) (show 0 ≤ (Sizes.t n i : ℝ)^6 by positivity))
    (show 0 ≤ (Sizes.p n : ℝ)^4 by positivity)
  exact_mod_cast hcostR.trans hscale

theorem selectedPackedHaloSetupReleaseCost_poly_le (ct cv : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b V : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      V ≤ cv*Sizes.p n →
      packedHaloSetupReleaseCost true (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (target+1) 2 (Sizes.s n i) (Sizes.t n i) a b V ≤ C*Sizes.t n i^6*Sizes.p n^4 := by
  obtain ⟨C,hfactor⟩ := selectedConstructedBoundaryFactorCost_poly_le ct
  obtain ⟨cw,hcw,hwidths⟩ := selectedInverseBoundaryWidths_le ct
  let cZ := cw+cv+1
  let K := 300000*cZ^3
  refine ⟨C+K,?_⟩
  filter_upwards [hfactor] with n hn
  intro h i _ u target a b V hu htarget hband ha hb hV
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let Z := cZ*p
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hst : s < t := h.good.lt i
  obtain ⟨hpt,hN,hq,hw,hG,hW,hbandP⟩ := hwidths n h i u target a b htarget hband
  have hZ : 1 ≤ Z := by dsimp only [Z,cZ]; nlinarith only [hp]
  have hwScale : cw*p ≤ Z := Nat.mul_le_mul_right p (by dsimp only [cZ]; omega)
  have hVZ : V ≤ Z := hV.trans (Nat.mul_le_mul_right p (by dsimp only [cZ]; omega : cv ≤ cZ))
  have hsetup := packedHaloSetupReleaseCost_poly hst ha hb hZ hVZ
    (hq.trans hwScale) (hw.trans hwScale) (hW.trans hwScale) (hG.trans hwScale)
  have hf := hn h i u target a b hu htarget hband ha hb
  have heq : 300000*t^2*Z^3 = K*t^2*p^3 := by dsimp only [Z,K]; ring
  rw [heq] at hsetup
  have htpow : t^2 ≤ t^6 := Nat.pow_le_pow_right ht (by decide)
  have hppow : p^3 ≤ p^4 := Nat.pow_le_pow_right hp (by decide)
  have hscale := Nat.mul_le_mul_left K (Nat.mul_le_mul htpow hppow)
  nlinarith only [hsetup,hf,hscale]

/-- Shared factor work is paid once, irrespective of the replica count. -/
theorem selectedPackedHaloSetupReleaseCost_scaled_volume_le (ct cv scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b V : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      V ≤ cv*Sizes.p n →
      scale*packedHaloSetupReleaseCost true (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (target+1) 2 (Sizes.s n i) (Sizes.t n i) a b V ≤ Sizes.T n := by
  obtain ⟨C,hcost⟩ := selectedPackedHaloSetupReleaseCost_poly_le ct cv
  filter_upwards [hcost,selectedAxisPolynomial_le_volume (scale*C) 4 6] with n hc hv
  intro h i _ u target a b V hu ht hband ha hb hV
  exact (Nat.mul_le_mul_left scale (hc h i u target a b V hu ht hband ha hb hV)).trans
    (by convert hv i using 1 <;> ring)

end IntegerMultBounds.MathlibTM2.Cost
