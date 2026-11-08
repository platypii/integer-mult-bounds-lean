module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRoundAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedRoundScalars
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStableInteriorBounds

/-! The original principal solve supplies normalization magnitude and canonical width room. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem cyclicPrincipal_round_magnitude {s t p u q a n : ℕ} [NeZero s]
    (hp : 0 < p)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (rhs : ZMod s → GaussianInt) (hrhs : ∀ i, ‖value q (rhs i)‖ ≤ (2 : ℝ)^2)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
      (fun i => (value q (rhs i)).re)) :
    ∀ i ∈ cyclicPrincipalVertices s a n, ‖x i‖ ≤ 4*(2 : ℝ)^(p+8) := by
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hAI := SchurDominance.dominates_mono _ Finset.univ (cyclicPrincipalVertices s a n) _
    (Finset.subset_univ _) hdom
  intro i hi
  have h := SchurDominance.solves_bound _ _ _ hμ hAI x _ hx ((2 : ℝ)^2)
    (fun j _ => (Complex.abs_re_le_norm _).trans (hrhs j)) i hi
  rw [div_div_eq_mul_div,div_one] at h
  have hpPow : (p : ℝ) ≤ (2 : ℝ)^p := by exact_mod_cast (Nat.lt_two_pow_self (n := p)).le
  rw [Real.norm_eq_abs]
  have hscale : 8*(p : ℝ)*(2 : ℝ)^2 ≤ 4*(2 : ℝ)^(p+8) := by
    rw [pow_add]
    norm_num
    nlinarith only [hpPow,pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p]
  exact h.trans (by simpa only [mul_comm] using hscale)

theorem cyclicPrincipal_finalRound_accuracy {A s t p u l target a n : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hp : 0 < p) (ha : a < s) (W : ℕ) (hW : 2*p+13 ≤ W)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (rhs G : ZMod s → GaussianInt) (hreal : ∀ i, (G i).im = 0)
    (x : ZMod s → ℝ) (tail : List (Fin (A+4))) :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let q := executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card) 2) 2
    let w := 2*q+8
    (∀ i, ‖value q (rhs i)‖ ≤ (2 : ℝ)^2) →
    (∀ i, Fits w (G i)) →
    SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
      (fun i => (value q (rhs i)).re) →
    PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (fun i => (value q (G i)).re) x (1/(2 : ℝ)^(target+1)) →
    PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (cyclicIntervalRead p W a (cstream A W
        (cyclicInterval a n (fun i => finalRoundWord w q p (inverseNormalizationShift p) (G i)))++tail))
      (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))
      (2/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^inverseNormalizationShift p) := by
  dsimp only
  intro hrhs hfits hx herror
  have hdim := cyclicRound_dimensions p u l target
    (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card
  have hmag := cyclicPrincipal_round_magnitude hp hdom rhs hrhs x hx
  exact cyclicRealFinalRound_accuracy hA _ _ _ _ _ (p+8) a n hdim.1 hdim.2.1
    (by omega) ha G hreal hfits x _
    ((div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))) hmag tail herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
