module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyRecoveryFast

/-! Both actual interior passes have a complete fast bound, including numerical setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedInteriorPair_fast_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (u target a b : ℕ), u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
        (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let firstTarget := initialSchurTarget p u bits 2
      let secondTarget := recoveryTarget p bits
      let recoveryExp := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
      (familyHaloInteriorGeometryCost p l s t u firstTarget 2 a b : ℝ)+
        (familyHaloInteriorGeometryCost p l s t u secondTarget recoveryExp a b : ℝ) ≤
          C*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hfast⟩ := familyInteriorPair_selected_fast_le ct 2
  obtain ⟨K,hK⟩ := selectedInteriorControls_fast_le ct
  refine ⟨D+(K : ℝ),by positivity,?_⟩
  filter_upwards [hK] with n hn
  intro h i _ u target a b hu htarget hband ha hb
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let firstTarget := initialSchurTarget p u bits 2
  let secondTarget := recoveryTarget p bits
  let recoveryExp := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have hθ := h.quarter_p_le_theta i
  have hbits : Nat.size (2*s+1) ≤ Nat.size t+2 := by
    apply Nat.size_le.mpr
    rw [pow_add]
    norm_num
    have := Nat.lt_size_self t
    omega
  have htbits := selectedAxisBits_le n i
  have hell := selectedAxisLog_le_precision h
  have hgeometry : Nat.size (2*s+1) ≤ 2*p := by
    have := h.thirteen_le_p
    dsimp only [p,s,t] at *
    omega
  have harith := hfast p u target s t a b hp hst hband hθ htarget hgeometry
  have hcontrols := hn h i u target a b hu htarget hband ha hb
  have hcontrolsR : (familyHaloControlCost p l s t u firstTarget 2 a b : ℝ)+
      (familyHaloControlCost p l s t u secondTarget recoveryExp a b : ℝ) ≤ (K : ℝ)*(t : ℝ)*(p : ℝ) := by
    exact_mod_cast hcontrols
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) :=
    Real.self_le_rpow_of_one_le hpR (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hpPow (show 0 ≤ (K : ℝ)*(t : ℝ) by positivity)
  change (familyHaloInteriorGeometryCost p l s t u firstTarget 2 a b : ℝ)+
    (familyHaloInteriorGeometryCost p l s t u secondTarget recoveryExp a b : ℝ) ≤
      (D+(K : ℝ))*(t : ℝ)*(p : ℝ)^(129/128 : ℝ)
  change (familyHaloInteriorGeometryCost p l s t u firstTarget 2 a b : ℝ)+
    (familyHaloInteriorGeometryCost p l s t u secondTarget recoveryExp a b : ℝ) ≤
      (familyHaloControlCost p l s t u firstTarget 2 a b : ℝ)+
        (familyHaloControlCost p l s t u secondTarget recoveryExp a b : ℝ)+
        D*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) at harith
  nlinarith only [harith,hcontrolsR,hscaled]

end IntegerMultBounds.MathlibTM2.Cost
