module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedRecoveryMagnitude

/-! The inherited publication error leaves room in the real-factor radius-two ball. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem publicationError_le_half (p target : ℕ) (hp : 3 ≤ p) :
    2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p) ≤ 1/2 := by
  have hpow : (8 : ℝ) ≤ (2 : ℝ)^p := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp
    norm_num at hh
    exact hh
  have hshift : (4 : ℝ) ≤ (2 : ℝ)^(inverseNormalizationShift p) := by
    have hh := inverseNormalizationShift_large p
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have htarget : 1/(2 : ℝ)^target ≤ 1 :=
    (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have ha : 2/(2 : ℝ)^p ≤ 1/4 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hb : (1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p) ≤ 1/4 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  linarith

theorem published_norm_le_two {s : ℕ} (p target : ℕ) (hp : 3 ≤ p)
    (active : Finset (ZMod s)) (f z : ZMod s → ℂ)
    (hz : ∀ i ∈ active, ‖z i‖ ≤ (3/2 : ℝ))
    (herror : PhaseCellInterface.ErrorOn active f z
      (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p))) :
    ∀ i ∈ active, ‖f i‖ ≤ 2 := by
  intro i hi
  have he := (herror i hi).trans (publicationError_le_half p target hp)
  have hn := norm_sub_le_norm_sub_add_norm_sub (f i) (z i) 0
  simp only [sub_zero] at hn
  linarith [hz i hi]

namespace ScalarPlacement.RecoveryAxisBounds
open IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
variable {s t p u l : ℕ} [NeZero s] {α gap : ℝ}

theorem ownedPublished_norm_le_two (axis : RecoveryAxisBounds s t p u l α gap)
    (target L k : ℕ) (hnear : t ≤ 2*s) (hL : 2 ≤ L)
    (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
    (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
    (hfit : L+2*(localityDepth p target*PhaseCellBand.width p u)+PhaseCellBand.width p u ≤ s)
    (hp : 3 ≤ p) (Fs : List (ZMod t → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1)
    (z f : ZMod s → ℂ) (hz : z ∈ axis.ownedTargets target L k hnear hL ha hb hfit Fs)
    (herror : PhaseCellInterface.ErrorOn (haloVertices s (cut s t L k) (cut s t L (k+1))) f
      (fun i => ((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i)
      (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^(inverseNormalizationShift p))) :
    ∀ i ∈ haloVertices s (cut s t L k) (cut s t L (k+1)), ‖f i‖ ≤ 2 := by
  apply published_norm_le_two p target hp _ f _ _ herror
  intro i hi
  apply axis.ownedTargets_normalized_norm_le target L k hnear hL ha hb hfit Fs hF z hz i
  obtain ⟨hl,hr⟩ := (mem_haloVertices _ _ i).mp hi
  apply (mem_haloVertices _ _ i).mpr
  constructor <;> omega

end ScalarPlacement.RecoveryAxisBounds

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
