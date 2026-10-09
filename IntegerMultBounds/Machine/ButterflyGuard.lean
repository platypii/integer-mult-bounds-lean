import IntegerMultBounds.Machine.ButterflySigned
import IntegerMultBounds.Networks.GaussianPrecision

/-! A single signed width covers every arithmetic stage of an individual-kernel
fallback. The guard follows from the actual dyadic numerator growth, including
all precision increments, rather than a supplied codec correctness assumption. -/
namespace IntegerMultBounds.Machine.ButterflyGuard
noncomputable section
open ButterflySigned
open Networks.GaussianPrecision

/-- Two growth bits per kernel, plus a constant guard and sign. -/
def halfWidth (p D : ℕ) := p+2*D+3
def width (p D : ℕ) := halfWidth p D+1

theorem width_linear (p D : ℕ) (hD : D≤p) : width p D ≤ 3*p+4 := by
  unfold width halfWidth
  omega

theorem precision_le (p D j : ℕ) (hj : j≤D) : p+j ≤ p+D := by omega

/-- All intermediate numerator bounds fit with room for the four-summand
butterfly, including a call made at the maximum permitted dependency depth. -/
theorem guard (p D j : ℕ) (hj : j≤D) :
    4*((2^p : ℕ)*4^j) < 2^(halfWidth p D) := by
  have hpow : 4*((2^p : ℕ)*4^j)=2^(p+2*j+2) := by
    rw [show (4:ℕ)=2^2 by norm_num,←pow_mul,←pow_add,←pow_add]
    congr 1
    omega
  rw [hpow]
  exact Nat.pow_lt_pow_right (by decide) (by unfold halfWidth; omega)

/-- A stored Gaussian dyadic has unique integer component numerators. -/
theorem numerators_unique (a b c d : ℤ) (p : ℕ)
    (h : complexValue a b p=complexValue c d p) : a=c ∧ b=d := by
  have hp : (2:ℂ)^p≠0 := pow_ne_zero _ (by norm_num)
  have he : (a:ℂ)+(b:ℂ)*Complex.I=(c:ℂ)+(d:ℂ)*Complex.I :=
    (div_left_inj' hp).mp h
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [Complex.add_re,Complex.intCast_re,Complex.mul_re,Complex.intCast_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at hre
  simp only [Complex.add_im,Complex.intCast_im,Complex.mul_im,Complex.intCast_re,
    Complex.I_re,Complex.I_im,mul_one,zero_mul,add_zero,zero_add] at him
  exact ⟨Int.cast_injective hre,Int.cast_injective him⟩

/-- The mathematical bounded-grid invariant bounds the actual stored numerators. -/
theorem represented_bound (a b : ℤ) (p M : ℕ) (h : BoundedGrid p M (complexValue a b p)) :
    |a|≤(M:ℤ) ∧ |b|≤(M:ℤ) := by
  obtain ⟨c,d,he,hc,hd⟩ := h
  have hp : (2:ℂ)^p≠0 := pow_ne_zero _ (by norm_num)
  have he' : complexValue a b p=complexValue c d p := by
    apply (eq_div_iff hp).mpr
    exact he
  obtain ⟨rfl,rfl⟩ := numerators_unique a b c d p he'
  exact ⟨hc,hd⟩

/-- For normalized input magnitude, the precision exponent itself bounds the
integer components. This supplies the initial invariant from the norm contract. -/
theorem normalized_bound (a b : ℤ) (p : ℕ) (h : ‖complexValue a b p‖≤1) :
    |a|≤(2^p:ℕ) ∧ |b|≤(2^p:ℕ) := by
  have hp : (2:ℂ)^p≠0 := pow_ne_zero _ (by norm_num)
  have he : complexValue a b p*(2:ℂ)^p=(a:ℂ)+(b:ℂ)*Complex.I := by
    exact div_mul_cancel₀ _ hp
  have hn : ‖(a:ℂ)+(b:ℂ)*Complex.I‖ ≤ (2:ℝ)^p := by
    rw [←he,norm_mul,norm_pow]
    norm_num only [Complex.norm_ofNat] at ⊢
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) p]
  have hr := (Complex.abs_re_le_norm ((a:ℂ)+(b:ℂ)*Complex.I)).trans hn
  have hi := (Complex.abs_im_le_norm ((a:ℂ)+(b:ℂ)*Complex.I)).trans hn
  simp at hr hi
  constructor
  · exact_mod_cast hr
  · exact_mod_cast hi

/-- The actual literal kernel list establishes both scale and bounded numerators
at every prefix, before the width guard is applied. -/
theorem prefix_grid {h : ℕ} (gs : List (ZMod 4 × Networks.BinaryWalsh.Address h))
    (f : Networks.BinaryWalsh.Arrays h) (p D j : ℕ)
    (hf : ∀ x,BoundedGrid p (2^p) (f x)) (hD : gs.length≤D) :
    (∀ x,BoundedGrid (p+(gs.take j).length) ((2^p)*4^(gs.take j).length)
      (Networks.BinaryWalsh.kernelRun (gs.take j) f x)) ∧
    4*((2^p)*4^(gs.take j).length) < 2^(halfWidth p D) := by
  refine ⟨bounded_kernelRun _ _ hf,guard p D _ ?_⟩
  simp only [List.length_take]
  omega

end
end IntegerMultBounds.Machine.ButterflyGuard
