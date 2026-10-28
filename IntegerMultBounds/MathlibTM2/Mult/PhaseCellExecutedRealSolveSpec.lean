module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedInverse
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealInputWord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellQuantizedSolveSpec
public import IntegerMultBounds.NLogN.PhaseCellBoundary

/-! The executed full-line inverse inhabits the real solver endpoint, with input rounding charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A s : ℕ} [NeZero s] {U : Type}

noncomputable def executedRealInverse (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (p u l target t : ℕ) (v : HS 303 Q A U) (b : ZMod s → ℝ) : ZMod s → ℝ :=
  let q := inverseFullInputPrecision p u l target s t
  let w := inverseFullInputWidth p u l target s t
  let F := fun i => realInputWord q (b i)
  let G := executedInverseOutput recovery hR hQ p u l target t v F
  fun i => (pairedCellRead q w (cstream A w (chirpLine s G)) i).re

theorem executedRealInverse_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p u l target t : ℕ} {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (v : HS 303 Q A U) :
    SolveSpec (realMatrix s t p u) Finset.univ Finset.univ (1/2)
      (executedRealInverse recovery hR hQ p u l target t v)
      (1/(2 : ℝ)^target+8*(p : ℝ)/(2 : ℝ)^(inverseFullInputPrecision p u l target s t)) := by
  letI : NeZero t := ⟨by have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne _); omega⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hA' := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  let q := inverseFullInputPrecision p u l target s t
  let quantize := fun (b : ZMod s → ℝ) i => (value q (realInputWord q (b i))).re
  have hspec : SolveSpec (realMatrix s t p u) Finset.univ Finset.univ (1/2)
      (executedRealInverse recovery hR hQ p u l target t v)
      (1/(2 : ℝ)^target+(1/(2 : ℝ)^q)/(1/(8*(p : ℝ)))) := by
    apply SolveSpec.of_rhs_rounding _ _ _ Finset.Subset.rfl _ hμ hA' _ _ _ quantize
    · intro b hb i hi
      exact realInputWord_error q (b i)
    · intro b hb y hy
      let F : ZMod s → GaussianInt := fun i => realInputWord q (b i)
      have hF : ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2 := by
        intro i
        exact (realInputWord_norm_le q (b i)).trans ((hb i (Finset.mem_univ i)).trans (by norm_num))
      have hz : Matrix.mulVec (fun i j => (realMatrix s t p u i j : ℂ)) (fun i => (y i : ℂ)) =
          (fun i => value q (F i)) := by
        funext i
        apply Complex.ext
        · simpa only [Matrix.mulVec,dotProduct,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
            Complex.ofReal_im,mul_zero,sub_zero,quantize,F] using hy i (Finset.mem_univ i)
        · simp only [Matrix.mulVec,dotProduct,Complex.im_sum,Complex.mul_im,Complex.ofReal_re,
            Complex.ofReal_im,mul_zero,zero_mul,add_zero,Finset.sum_const_zero,F,realInputWord_value_im]
      obtain ⟨v',n,huser,hcost,he,herror⟩ := executedInverseOutput_spec recovery hR hQ hA hp hwidth hα hst hu hαu
        hθ hgap hbudget hband hpad F hF v (fun i => (y i : ℂ)) hz
      intro i hi
      have hr := (Complex.abs_re_le_norm _).trans (herror i)
      simpa only [executedRealInverse,Real.norm_eq_abs,Complex.sub_re,Complex.ofReal_re] using hr
  have he : 1/(2 : ℝ)^target+(1/(2 : ℝ)^q)/(1/(8*(p : ℝ))) =
      1/(2 : ℝ)^target+8*(p : ℝ)/(2 : ℝ)^q := by field_simp <;> ring
  rwa [he] at hspec

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
