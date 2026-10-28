module

public import IntegerMultBounds.MathlibTM2.Mult.B0Generic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The `B̃₀` interface for a small-gap inverse computed through the rounded
matrix. If the computed inverse is within `e` of `L (v/2) / 2^j`, where `L`
inverts the rounded operator and differs from the exact inverse `J` by `δ₀`,
then with `4p ≤ 2^j` it keeps the unit disk and approximates `J (v/2) / 2^j`;
hence `B̃₀` satisfies the pipeline interface for the normalized target
`B₀ J / 2^j` of the small-gap factorization. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.FastB0

open IntegerMultBounds IntegerMultBounds.NLogN
open ContinuousLinearMap

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

theorem smallgap_inverse_value_spec (p j : ℕ) (J L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJn : ‖J‖≤4*(p : ℝ)) (hj : 4*(p : ℝ)≤2^j) {δ₀ e : ℝ} (hdiff : ‖L-J‖≤δ₀)
    (hsmall : e+δ₀/2≤1/2) (v y : ZMod s → ℂ) (hv : ‖v‖≤1)
    (hJt : ‖y-((2 : ℂ)^j)⁻¹ • L ((1/2 : ℂ) • v)‖≤e) :
    ‖y‖≤1 ∧ 2^p*‖y-(((2 : ℂ)^j)⁻¹ • J) ((1/2 : ℂ) • v)‖≤2^p*(e+δ₀/2) := by
  have hc : ‖((2 : ℂ)^j)⁻¹‖≤1 := by
    rw [norm_inv, norm_pow, RCLike.norm_two]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hcR : ‖((2 : ℂ)^j)⁻¹‖=((2 : ℝ)^j)⁻¹ := by rw [norm_inv, norm_pow, RCLike.norm_two]
  have hhalf : ‖(1/2 : ℂ) • v‖≤1/2 := by
    rw [norm_smul, norm_div, norm_one, RCLike.norm_two]; linarith
  have hδ0 : 0≤δ₀ := (norm_nonneg _).trans hdiff
  have hLJ : ‖((2 : ℂ)^j)⁻¹ • L ((1/2 : ℂ) • v)-(((2 : ℂ)^j)⁻¹ • J) ((1/2 : ℂ) • v)‖≤δ₀/2 := by
    rw [smul_apply, ←smul_sub, ←sub_apply, norm_smul]
    calc ‖((2 : ℂ)^j)⁻¹‖*‖(L-J) ((1/2 : ℂ) • v)‖≤1*(δ₀*(1/2)) :=
          mul_le_mul hc ((le_opNorm _ _).trans (mul_le_mul hdiff hhalf (norm_nonneg _) hδ0))
            (norm_nonneg _) zero_le_one
      _=δ₀/2 := by ring
  have herr : ‖y-(((2 : ℂ)^j)⁻¹ • J) ((1/2 : ℂ) • v)‖≤e+δ₀/2 :=
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (hJt) hLJ)
  have hJv : ‖(((2 : ℂ)^j)⁻¹ • J) ((1/2 : ℂ) • v)‖≤1/2 := by
    rw [smul_apply, norm_smul, hcR]
    have hpos : (0 : ℝ)<2^j := by positivity
    calc ((2 : ℝ)^j)⁻¹*‖J ((1/2 : ℂ) • v)‖≤((2 : ℝ)^j)⁻¹*(4*p*(1/2)) := by
          gcongr
          exact (le_opNorm _ _).trans (mul_le_mul hJn hhalf (norm_nonneg _) (by positivity))
      _≤1/2 := by
          rw [inv_mul_le_iff₀ hpos]
          nlinarith
  refine ⟨?_, by gcongr⟩
  have h1 := norm_sub_norm_le (y) ((((2 : ℂ)^j)⁻¹ • J) ((1/2 : ℂ) • v))
  linarith

theorem smallgap_inverse_spec (p j : ℕ) (J L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJn : ‖J‖≤4*(p : ℝ)) (hj : 4*(p : ℝ)≤2^j) {δ₀ e : ℝ} (hdiff : ‖L-J‖≤δ₀)
    (hsmall : e+δ₀/2≤1/2) (Jt : (ZMod s → ℂ) → ZMod s → ℂ)
    (hJt : ∀ v : ZMod s → ℂ, ‖v‖≤1 → ‖Jt v-((2 : ℂ)^j)⁻¹ • L ((1/2 : ℂ) • v)‖≤e)
    (v : ZMod s → ℂ) (hv : ‖v‖≤1) :
    ‖Jt v‖≤1 ∧ 2^p*‖Jt v-(((2 : ℂ)^j)⁻¹ • J) ((1/2 : ℂ) • v)‖≤2^p*(e+δ₀/2) := by
  exact smallgap_inverse_value_spec p j J L hJn hj hdiff hsmall v (Jt v) hv (hJt v hv)

/-- The pipeline interface for `B̃₀` built on a small-gap computed inverse. -/
theorem smallgap_resampB₀_spec (p j : ℕ) (J L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJn : ‖J‖≤4*(p : ℝ)) (hj : 4*(p : ℝ)≤2^j) {δ₀ e : ℝ} (hdiff : ‖L-J‖≤δ₀)
    (hsmall : e+δ₀/2≤1/2) (Jt : (ZMod s → ℂ) → ZMod s → ℂ)
    (hJt : ∀ v : ZMod s → ℂ, ‖v‖≤1 → ‖Jt v-((2 : ℂ)^j)⁻¹ • L ((1/2 : ℂ) • v)‖≤e)
    (df : ZMod s → ℝ) (hdf : ∀ ℓ, 2^p*‖rhoC p (df ℓ : ℂ)-(dPrime s t α ℓ : ℂ)‖≤2)
    (hdf1 : ∀ ℓ, ‖rhoC p (df ℓ : ℂ)‖≤1) :
    ApproxMap p (resampB₀Of (t := t) p Jt df) (((2 : ℂ)^j)⁻¹ • resampB₀ s t α J)
        (6+2^p*(e+δ₀/2)) ∧
      ∀ w : ZMod t → ℂ, ‖w‖≤1 → ‖resampB₀Of (t := t) p Jt df w‖≤1 := by
  rw [←resampB₀_smul]
  exact resampB₀Of_spec Jt df (fun v hv => smallgap_inverse_spec p j J L hJn hj hdiff hsmall Jt
    hJt v hv) hdf hdf1

end IntegerMultBounds.MathlibTM2.Mult.FastB0
