module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyInteriorFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedSetup

/-! Interior geometry accepts any target whose actual width is linear in p.
Joint-boundary precision therefore needs sizing, not a new arithmetic proof. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open Filter IntegerMultBounds.MathlibTM2.Mult

theorem familyInteriorGeometry_width_fast_le (cl cw cr : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ p l target rhsExp s t u a b : ℕ,
      1 ≤ p → l ≤ cl*p → executionWidth p l target rhsExp ≤ cw*p → 2^l ≤ cr*p →
      (familyHaloInteriorGeometryCost p l s t u target rhsExp a b : ℝ) ≤
        (familyHaloControlCost p l s t u target rhsExp a b : ℝ)+
        (haloInterior s t (PhaseCellBand.width p u) a b).card*
          (C*(p : ℝ)^(129/128 : ℝ))+
        (t-s+1 : ℕ)*(D*(2^l : ℕ)*(p : ℝ)^(129/128 : ℝ)) := by
  obtain ⟨C,hC,hcoord⟩ := cachedBatchCoordinate_fast_le cl cw
  obtain ⟨D,hD,hcell⟩ := cachedBatchCell_fast_le cl cw cr
  refine ⟨C+44*cw,D,by positivity,hD,?_⟩
  intro p l target rhsExp s t u a b hp hl hw hr
  have hc := hcoord p l target rhsExp hp hl hw
  have hd := hcell p l target rhsExp hp hl hw hr
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow := Real.self_le_rpow_of_one_le hpR (by norm_num : (1 : ℝ) ≤ 129/128)
  have hwR := (Nat.cast_le (α := ℝ)).mpr hw
  push_cast at hwR
  have hwidth := hwR.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg cw))
  have hrow : (cachedBatchCoordinateCost p l target rhsExp : ℝ)+
      44*executionWidth p l target rhsExp ≤ (C+44*cw)*(p : ℝ)^(129/128 : ℝ) := by
    nlinarith only [hc,hwidth]
  rw [familyHaloInteriorGeometryCost_eq]
  push_cast at hd ⊢
  exact add_le_add (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg _)))
    (mul_le_mul_of_nonneg_left hd (by positivity))

/-- The derived ring length pays padded cells in axis volume for any target.
Only its actual linear working-width bound depends on the precision choice. -/
theorem familyInteriorGeometry_ring_fast_le (cw : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ p target rhsExp s t u a b : ℕ, ∀ [NeZero s],
      1 ≤ p → s < t → 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1 →
      executionWidth p (haloInverseRingLog s t) target rhsExp ≤ cw*p →
      (familyHaloInteriorGeometryCost p (haloInverseRingLog s t) s t u target rhsExp a b : ℝ) ≤
        (familyHaloControlCost p (haloInverseRingLog s t) s t u target rhsExp a b : ℝ)+
          E*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,D,hC,hD,hfast⟩ := familyInteriorGeometry_width_fast_le 20 cw 20
  refine ⟨C+8*D,by positivity,?_⟩
  intro p target rhsExp s t u a b _ hp hst htheta hw
  obtain ⟨hl,hr⟩ := haloInverseRingLog_bounds hp hst htheta
  have hf := hfast p _ target rhsExp s t u a b hp hl hw hr
  have hI : (haloInterior s t (PhaseCellBand.width p u) a b).card ≤ t := by
    have h := Finset.card_le_univ (s := haloInterior s t (PhaseCellBand.width p u) a b)
    simp only [ZMod.card] at h
    omega
  have hiR := (Nat.cast_le (α := ℝ)).mpr hI
  have hv := (Nat.cast_le (α := ℝ)).mpr (haloInverseRing_paddedVolume_le hst)
  have hi := mul_le_mul_of_nonneg_right hiR
    (by positivity : 0 ≤ C*(p : ℝ)^(129/128 : ℝ))
  have hc := mul_le_mul_of_nonneg_right hv
    (by positivity : 0 ≤ D*(p : ℝ)^(129/128 : ℝ))
  push_cast at hf hv hc
  nlinarith only [hf,hi,hc]

/-- Selected setup controls also accept arbitrary working targets. The whole
geometry bill therefore has the fast axis-volume bound under actual sizing. -/
theorem selectedInteriorGeometry_width_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ u target rhsExp a b : ℕ,
      let l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)
      executionWidth (Sizes.p n) l target rhsExp ≤ cw*Sizes.p n →
      u ≤ Sizes.p n → PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      (familyHaloInteriorGeometryCost (Sizes.p n) l (Sizes.s n i) (Sizes.t n i)
        u target rhsExp a b : ℝ) ≤ C*(Sizes.t n i : ℝ)*(Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨E,hE,hgeometry⟩ := familyInteriorGeometry_ring_fast_le cw
  obtain ⟨K,hcontrol⟩ := familyHaloControlCost_selected_fast_le cw 20 20
  refine ⟨E+K,by positivity,?_⟩
  filter_upwards [hcontrol] with n hn
  intro h i _ u target rhsExp a b
  dsimp only
  intro hw hu hband ha hb
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  obtain ⟨hl,hr⟩ := haloInverseRingLog_bounds hp (h.good.lt i) (h.quarter_p_le_theta i)
  have hc := (Nat.cast_le (α := ℝ)).mpr (hn h i _ u target rhsExp a b hw hl hr hu hband ha hb)
  have hg := hgeometry _ target rhsExp _ _ u a b hp (h.good.lt i) (h.quarter_p_le_theta i) hw
  have hpR : (1 : ℝ) ≤ Sizes.p n := by exact_mod_cast hp
  have hpow := Real.self_le_rpow_of_one_le hpR (by norm_num : (1 : ℝ) ≤ 129/128)
  have hs := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ (K : ℝ)*(Sizes.t n i : ℝ))
  push_cast at hc
  nlinarith only [hc,hg,hs]

end IntegerMultBounds.MathlibTM2.Cost
