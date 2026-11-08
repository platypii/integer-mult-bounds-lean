module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetOwnedRecoverySolutions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentSolutionMagnitude
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRoundScalars

/-! Stability supplies publication magnitude for the actual floor-owned jobs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- Principal stability for a complex half-grid right hand side. -/
theorem halfGridSolution_norm_le {s : ℕ} (p : ℕ) (hp : 0 < p)
    (M : Matrix (ZMod s) (ZMod s) ℝ) (active : Finset (ZMod s))
    (hdom : DominatesOn M active (1/(8*(p : ℝ))))
    (F z : ZMod s → ℂ) (hF : ∀ i, ‖F i‖ ≤ 1)
    (hre : Solves M active (fun i => (z i).re) (fun i => ((1/2 : ℂ)*F i).re))
    (him : Solves M active (fun i => (z i).im) (fun i => ((1/2 : ℂ)*F i).im)) :
    ∀ i ∈ active, ‖z i‖ ≤ 6*(p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hunit i : ‖(1/2 : ℂ)*F i‖ ≤ (1/2 : ℝ) := by
    rw [norm_mul]
    norm_num
    linarith [hF i]
  have hr := solves_bound M active (1/(8*(p : ℝ))) (by positivity) hdom
    (fun i => (z i).re) _ hre (1/2) (by intro i _; exact (Complex.abs_re_le_norm _).trans (hunit i))
  have hi := solves_bound M active (1/(8*(p : ℝ))) (by positivity) hdom
    (fun i => (z i).im) _ him (1/2) (by intro i _; exact (Complex.abs_im_le_norm _).trans (hunit i))
  have hquot : (1/2 : ℝ)/(1/(8*(p : ℝ))) = 4*(p : ℝ) := by field_simp; ring
  intro i hmem
  have hr' := hr i hmem
  have hi' := hi i hmem
  rw [hquot] at hr' hi'
  have hrSq := mul_self_le_mul_self (abs_nonneg ((z i).re)) hr'
  have hiSq := mul_self_le_mul_self (abs_nonneg ((z i).im)) hi'
  rw [abs_mul_abs_self] at hrSq hiSq
  have hs := Complex.norm_mul_self_eq_normSq (z i)
  rw [Complex.normSq_apply] at hs
  nlinarith [norm_nonneg (z i)]

namespace RecoveryAxisBounds
variable {s t p u l : ℕ} [NeZero s] {α gap : ℝ}
variable (h : RecoveryAxisBounds s t p u l α gap) (target L k : ℕ)
variable (hnear : t ≤ 2*s) (hL : 2 ≤ L)
variable (ha : localityDepth p target*PhaseCellBand.width p u ≤ cut s t L k)
variable (hb : cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u ≤ s)
variable (hfit : L+2*(localityDepth p target*PhaseCellBand.width p u)+PhaseCellBand.width p u ≤ s)

theorem ownedTargets_norm_le (Fs : List (ZMod t → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    ∀ z ∈ h.ownedTargets target L k hnear hL ha hb hfit Fs,
      ∀ i ∈ haloVertices s (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
        (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u), ‖z i‖ ≤ 6*(p : ℝ) := by
  let active := haloVertices s (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
    (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u)
  have hdom := dominates_mono (realMatrix s t p u) Finset.univ active
    (1/(8*(p : ℝ))) (Finset.subset_univ _) h.hdom
  have hs := h.ownedTargets_solves target L k hnear hL ha hb hfit Fs hF
  change List.Forall₂ (fun (F : ZMod t → GaussianInt) (z : ZMod s → ℂ) =>
    Solves (realMatrix s t p u) active (fun i => (z i).re)
      (fun i => ((1/2 : ℂ)*value p (F (rowIndex s t i))).re) ∧
    Solves (realMatrix s t p u) active (fun i => (z i).im)
      (fun i => ((1/2 : ℂ)*value p (F (rowIndex s t i))).im)) _ _ at hs
  generalize h.ownedTargets target L k hnear hL ha hb hfit Fs = Zs at hs ⊢
  revert hF
  induction hs with
  | nil => simp
  | @cons F z Fs Zs hpair hs ih =>
    intro hF z' hz i hi
    rcases List.mem_cons.mp hz with hz | hz
    · subst z'
      exact halfGridSolution_norm_le p (by have := h.hp; omega) _ active hdom
        (fun i => value p (F (rowIndex s t i))) z (fun i => hF F (by simp) _) hpair.1 hpair.2 i hi
    · exact ih (fun F hmem => hF F (by simp [hmem])) z' hz i hi

theorem ownedTargets_normalized_norm_le (Fs : List (ZMod t → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    ∀ z ∈ h.ownedTargets target L k hnear hL ha hb hfit Fs,
      ∀ i ∈ haloVertices s (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
        (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u),
        ‖((2 : ℂ)^(inverseNormalizationShift p))⁻¹*z i‖ ≤ (3/2 : ℝ) := by
  intro z hz i hi
  have hbound := h.ownedTargets_norm_le target L k hnear hL ha hb hfit Fs hF z hz i hi
  have hj := inverseNormalizationShift_large p
  have hpos : (0 : ℝ) < (2 : ℝ)^(inverseNormalizationShift p) := by positivity
  rw [norm_mul,norm_inv,norm_pow]
  norm_num only [Complex.norm_ofNat]
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hpos).mpr
  nlinarith

theorem ownedTargets_round_magnitude (Fs : List (ZMod t → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    ∀ z ∈ (h.ownedTargets target L k hnear hL ha hb hfit Fs).reverse,
      ∀ i ∈ haloVertices s (cut s t L k) (cut s t L (k+1)),
        ‖z i‖ ≤ 4*(2 : ℝ)^(p+8) := by
  have hbound := h.ownedTargets_norm_le target L k hnear hL ha hb hfit Fs hF
  intro z hz i hi
  have hi' : i ∈ haloVertices s (cut s t L k-localityDepth p target*PhaseCellBand.width p u)
      (cut s t L (k+1)+localityDepth p target*PhaseCellBand.width p u) := by
    obtain ⟨hl,hr⟩ := (mem_haloVertices _ _ i).mp hi
    apply (mem_haloVertices _ _ i).mpr
    constructor <;> omega
  have hzbound := hbound z (List.mem_reverse.mp hz) i hi'
  have hp : (p : ℝ) ≤ (2 : ℝ)^p := by exact_mod_cast (show p < 2^p from Nat.lt_two_pow_self).le
  have hpow : (2 : ℝ)^(p+8) = 256*(2 : ℝ)^p := by rw [pow_add]; norm_num; ring
  rw [hpow]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) p]

omit [NeZero s] in
theorem owned_normalization_width :
    2*p+13 ≤ packedHaloCommonWidth p l s u (target+1) 2 := by
  have hd := packedRound_dimensions p u l target s
  dsimp only [executionPrecision] at hd
  dsimp only [packedHaloCommonWidth,executionWidth]
  omega

end RecoveryAxisBounds
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
