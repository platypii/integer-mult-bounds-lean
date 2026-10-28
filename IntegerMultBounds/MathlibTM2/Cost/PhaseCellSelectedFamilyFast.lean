module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFamilyRhsFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyGeneratedBoundaryRhs

/-! The actual generated family line satisfies its fast bound, with no separate
boundary RHS gather remainder. Shared construction multiplicities remain separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedFamilyBoundaryRhs_fast_le (ct : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let band := PhaseCellBand.width p u
      let N := (haloBoundary s t band a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let q := executionPrecision p (haloInverseRingLog s t) (initialSchurTarget p u bits 2) 2
      familyGeneratedBoundaryRhsCost (2^15*p) q s t u band a b ≤ C*t*p := by
  let cw := 1032+8*ct
  obtain ⟨C,hC⟩ := familyGeneratedBoundaryRhs_selected_fast_le (2^15) cw
  refine ⟨C,?_⟩
  intro n h i _ u target a b hu htarget hband ha hb
  dsimp only
  have hw := selectedInverseWorkingWidth_le ct h i u target a b htarget hband
  apply hC n h i _ _ u _ a b (by rfl) _ hu hband ha hb
  exact (show executionPrecision _ _ _ _ ≤ executionWidth _ _ _ _ by
    dsimp only [executionPrecision,executionWidth]; omega).trans hw

theorem selectedFamilyLine_fast_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      (generatedFamilyComplexGeometryLineCost p u l s t a b target : ℝ) ≤
        C*((t+(t-s)*band^2 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hfast⟩ := selectedFamilyLine_rhs_fast_le ct
  obtain ⟨D,hD⟩ := selectedFamilyBoundaryRhs_fast_le ct
  refine ⟨K+2*(D : ℝ),by positivity,?_⟩
  filter_upwards [hfast] with n hn
  intro h i _ u target a b hu htarget hband ha hb
  dsimp only
  have hk := hn h i u target a b hu htarget hband ha hb
  have hd := hD n h i u target a b hu htarget hband ha hb
  dsimp only at hk hd
  have hdR := (show ((familyGeneratedBoundaryRhsCost _ _ _ _ _ _ _ _ : ℕ) : ℝ) ≤
      (D : ℝ)*(Sizes.t n i : ℝ)*(Sizes.p n : ℝ) by exact_mod_cast hd)
  have hp : (1 : ℝ) ≤ Sizes.p n := by exact_mod_cast (show 1 ≤ Sizes.p n by have := h.thirteen_le_p; omega)
  have hpow : (Sizes.p n : ℝ) ≤ (Sizes.p n : ℝ)^(129/128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp (by norm_num)
  have hvolume : (Sizes.t n i : ℝ) ≤
      ((Sizes.t n i+(Sizes.t n i-Sizes.s n i)*(PhaseCellBand.width (Sizes.p n) u)^2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_add_right (Sizes.t n i) _)
  have hscale := mul_le_mul hvolume hpow (by positivity : (0 : ℝ) ≤ Sizes.p n) (by positivity)
  have hcharge := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg D)
  have hcharge' : (D : ℝ)*(Sizes.t n i : ℝ)*(Sizes.p n : ℝ) ≤
      (D : ℝ)*((Sizes.t n i+(Sizes.t n i-Sizes.s n i)*(PhaseCellBand.width (Sizes.p n) u)^2 : ℕ) : ℝ)*
        (Sizes.p n : ℝ)^(129/128 : ℝ) := by
    simpa only [mul_assoc] using hcharge
  calc
    _ ≤ _ := hk
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hdR (by norm_num : (0 : ℝ) ≤ 2)) (le_refl _)
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hcharge' (by norm_num : (0 : ℝ) ≤ 2)) (le_refl _)
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Cost
