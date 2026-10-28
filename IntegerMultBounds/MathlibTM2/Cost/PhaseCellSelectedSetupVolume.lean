module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorConstruction
public import IntegerMultBounds.MathlibTM2.Cost.PolynomialVolume

/-! One selected family's setup fits below whole-box volume. The number of
 distinct setup keys and their executed grouping remain separate obligations. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedSetupPolynomial_le_volume (A : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (Sizes.d n),
      A * Sizes.t n i ^ 6 * Sizes.p n ^ 4 ≤ Sizes.T n := by
  filter_upwards [ml_poly_r_le_T (A*6^4) 4 6] with n hn i
  calc
    A * Sizes.t n i ^ 6 * Sizes.p n ^ 4 ≤
        A * Sizes.r n ^ 6 * Sizes.p n ^ 4 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (mt_t_le_r n i) 6))
    _ = (A*6^4)*Sizes.b n ^ 4*Sizes.r n ^ 6 := by simp only [Sizes.p,mul_pow]; ring
    _ ≤ Sizes.T n := hn

theorem selectedFamilySetup_volume_le (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ A u target a b : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      (generatedFamilyComplexSetupCostBound A (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (Sizes.s n i) (Sizes.t n i) a b target : ℝ) ≤ Sizes.T n := by
  obtain ⟨C,hC,hsetup⟩ := selectedFamilySetup_poly_le ct
  filter_upwards [hsetup,selectedSetupPolynomial_le_volume ⌈C⌉₊] with n hs hv
  intro h i _ A u target a b hu htarget hband ha hb
  have hc := hs h i A u target a b hu htarget hband ha hb
  dsimp only at hc
  have hvolume : (⌈C⌉₊ : ℝ)*(Sizes.t n i : ℝ)^6*(Sizes.p n : ℝ)^4 ≤ Sizes.T n := by
    exact_mod_cast hv i
  exact hc.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity)) (by positivity)).trans hvolume)

end IntegerMultBounds.MathlibTM2.Cost
