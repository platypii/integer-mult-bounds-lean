module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyControlRhsRemainder
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyKernelVolume

/-! The generated family line has only boundary RHS gathering outside its fast allowance. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedFamilyLine_rhs_fast_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      let N := (haloBoundary s t band a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
      let w := executionWidth p l (initialSchurTarget p u bits 2) 2
      (generatedFamilyComplexGeometryLineCost p u l s t a b target : ℝ) ≤
        2*(familyGeneratedBoundaryRhsCost (2^15*p) q s t u band a b : ℝ)+
          C*((t+(t-s)*band^2 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hkernel⟩ := familyComplexGeometry_selected_gap_fast_le ct 2
  obtain ⟨D,hD⟩ := selectedFamilyControls_rhs_fast_le ct
  refine ⟨K+(D : ℝ),by positivity,?_⟩
  filter_upwards [hD] with n hn
  intro h i _ u target a b hu htarget hband ha hb
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let volume := t+(t-s)*band^2
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
  have hk := hkernel p u target s t a b hp hst hband hθ htarget hgeometry
  have hc := hn h i u target a b hu htarget hband ha hb
  have hcR : (familyComplexControlRemainingCost p u l s t a b target : ℝ) ≤
      2*(familyGeneratedBoundaryRhsCost (2^15*p) q s t u band a b : ℝ)+(D : ℝ)*(t : ℝ)*(p : ℝ) := by
    exact_mod_cast hc
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ)^(129/128 : ℝ) :=
    Real.self_le_rpow_of_one_le hpR (by norm_num)
  have hvolume : (t : ℝ) ≤ volume := by exact_mod_cast (show t ≤ volume by dsimp only [volume]; omega)
  have hlinear := mul_le_mul_of_nonneg_left hpPow (show 0 ≤ (D : ℝ)*(t : ℝ) by positivity)
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hvolume (Nat.cast_nonneg D))
    (Real.rpow_nonneg (Nat.cast_nonneg p) (129/128 : ℝ))
  change (generatedFamilyComplexGeometryLineCost p u l s t a b target : ℝ) ≤
    2*(familyGeneratedBoundaryRhsCost (2^15*p) q s t u band a b : ℝ)+
      (K+(D : ℝ))*(volume : ℝ)*(p : ℝ)^(129/128 : ℝ)
  change (generatedFamilyComplexGeometryLineCost p u l s t a b target : ℝ) ≤
    (familyComplexControlRemainingCost p u l s t a b target : ℝ)+
      K*(volume : ℝ)*(p : ℝ)^(129/128 : ℝ) at hk
  calc
    _ ≤ (familyComplexControlRemainingCost p u l s t a b target : ℝ)+
        K*(volume : ℝ)*(p : ℝ)^(129/128 : ℝ) := hk
    _ ≤ (2*(familyGeneratedBoundaryRhsCost (2^15*p) q s t u band a b : ℝ)+
        (D : ℝ)*(t : ℝ)*(p : ℝ))+K*(volume : ℝ)*(p : ℝ)^(129/128 : ℝ) :=
      add_le_add hcR le_rfl
    _ ≤ (2*(familyGeneratedBoundaryRhsCost (2^15*p) q s t u band a b : ℝ)+
        (D : ℝ)*(volume : ℝ)*(p : ℝ)^(129/128 : ℝ))+K*(volume : ℝ)*(p : ℝ)^(129/128 : ℝ) :=
      add_le_add (add_le_add le_rfl (hlinear.trans hscaled)) le_rfl
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Cost
