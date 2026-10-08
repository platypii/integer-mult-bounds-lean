import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The fixed-point approximation framework of Harvey and van der Hoeven,
Sections 2.2 and 2.6. Proved: round-towards-zero at precision `p` does not
increase the norm and errs by less than `√2 / 2^p`; the error of applying an
approximate contraction to an approximate input adds (Lemma 2.7); composition
of approximations adds errors (Corollary 2.8); the bilinear version (Lemma 2.9)
and rounded complex multiplication (Corollary 2.10); and applying an
approximation slice by slice keeps its error and norm bound (the one-coordinate
case of Lemma 2.11). Errors are stated as bounds, not as suprema, and no cost
model is attached. -/

open Complex

namespace IntegerMultBounds.NLogN

/-- Round a real toward zero. -/
noncomputable def rho0 (x : ℝ) : ℤ := if 0 ≤ x then ⌊x⌋ else ⌈x⌉

theorem abs_rho0_le (x : ℝ) : |(rho0 x : ℝ)| ≤ |x| := by
  unfold rho0
  split_ifs with h
  · have h1 := Int.floor_le x
    have h2 : (0 : ℝ) ≤ ⌊x⌋ := by exact_mod_cast Int.floor_nonneg.mpr h
    rw [abs_of_nonneg h2, abs_of_nonneg h]
    exact h1
  · push Not at h
    have h1 := Int.le_ceil x
    have h2 : (⌈x⌉ : ℝ) ≤ 0 := by exact_mod_cast Int.ceil_nonpos.mpr h.le
    rw [abs_of_nonpos h2, abs_of_neg h]
    linarith

theorem abs_rho0_sub_lt (x : ℝ) : |(rho0 x : ℝ) - x| < 1 := by
  unfold rho0
  split_ifs with h
  · have h1 := Int.floor_le x
    have h2 := Int.lt_floor_add_one x
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  · have h1 := Int.le_ceil x
    have h2 := Int.ceil_lt_add_one x
    rw [abs_sub_lt_iff]
    constructor <;> linarith

/-- Round a complex number toward zero, componentwise, at `p` fractional bits. -/
noncomputable def rhoC (p : ℕ) (u : ℂ) : ℂ :=
  ⟨(rho0 (2 ^ p * u.re) : ℝ) / 2 ^ p, (rho0 (2 ^ p * u.im) : ℝ) / 2 ^ p⟩

theorem rhoC_re (p : ℕ) (u : ℂ) : (rhoC p u).re = (rho0 (2 ^ p * u.re) : ℝ) / 2 ^ p := rfl

theorem rhoC_im (p : ℕ) (u : ℂ) : (rhoC p u).im = (rho0 (2 ^ p * u.im) : ℝ) / 2 ^ p := rfl

theorem norm_rhoC_le (p : ℕ) (u : ℂ) : ‖rhoC p u‖ ≤ ‖u‖ := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  rw [Complex.norm_def, Complex.norm_def, Complex.normSq_apply, Complex.normSq_apply]
  apply Real.sqrt_le_sqrt
  rw [rhoC_re, rhoC_im]
  have h1 : |(rho0 (2 ^ p * u.re) : ℝ)| ≤ |2 ^ p * u.re| := abs_rho0_le _
  have h2 : |(rho0 (2 ^ p * u.im) : ℝ)| ≤ |2 ^ p * u.im| := abs_rho0_le _
  have e1 : (rho0 (2 ^ p * u.re) : ℝ) / 2 ^ p * ((rho0 (2 ^ p * u.re) : ℝ) / 2 ^ p)
      = |(rho0 (2 ^ p * u.re) : ℝ)| ^ 2 / (2 ^ p) ^ 2 := by
    rw [sq_abs]; ring
  have e2 : (rho0 (2 ^ p * u.im) : ℝ) / 2 ^ p * ((rho0 (2 ^ p * u.im) : ℝ) / 2 ^ p)
      = |(rho0 (2 ^ p * u.im) : ℝ)| ^ 2 / (2 ^ p) ^ 2 := by
    rw [sq_abs]; ring
  have f1 : u.re * u.re = |2 ^ p * u.re| ^ 2 / (2 ^ p) ^ 2 := by
    rw [sq_abs]; field_simp
  have f2 : u.im * u.im = |2 ^ p * u.im| ^ 2 / (2 ^ p) ^ 2 := by
    rw [sq_abs]; field_simp
  rw [e1, e2, f1, f2]
  have g1 : |(rho0 (2 ^ p * u.re) : ℝ)| ^ 2 ≤ |2 ^ p * u.re| ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have g2 : |(rho0 (2 ^ p * u.im) : ℝ)| ^ 2 ≤ |2 ^ p * u.im| ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hp2 : (0 : ℝ) < (2 ^ p) ^ 2 := by positivity
  apply add_le_add <;> exact div_le_div_of_nonneg_right (by assumption) hp2.le

theorem norm_rhoC_sub_lt (p : ℕ) (u : ℂ) : ‖rhoC p u - u‖ < Real.sqrt 2 / 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hre : |(rhoC p u - u).re| < 1 / 2 ^ p := by
    rw [Complex.sub_re, rhoC_re]
    have := abs_rho0_sub_lt (2 ^ p * u.re)
    have e : (rho0 (2 ^ p * u.re) : ℝ) / 2 ^ p - u.re
        = ((rho0 (2 ^ p * u.re) : ℝ) - 2 ^ p * u.re) / 2 ^ p := by
      field_simp
    rw [e, abs_div, abs_of_pos hp]
    exact div_lt_div_of_pos_right this hp
  have him : |(rhoC p u - u).im| < 1 / 2 ^ p := by
    rw [Complex.sub_im, rhoC_im]
    have := abs_rho0_sub_lt (2 ^ p * u.im)
    have e : (rho0 (2 ^ p * u.im) : ℝ) / 2 ^ p - u.im
        = ((rho0 (2 ^ p * u.im) : ℝ) - 2 ^ p * u.im) / 2 ^ p := by
      field_simp
    rw [e, abs_div, abs_of_pos hp]
    exact div_lt_div_of_pos_right this hp
  rw [Complex.norm_def, Complex.normSq_apply]
  have hbound : (rhoC p u - u).re * (rhoC p u - u).re + (rhoC p u - u).im * (rhoC p u - u).im
      < 2 / (2 ^ p) ^ 2 := by
    have a1 : (rhoC p u - u).re * (rhoC p u - u).re = |(rhoC p u - u).re| ^ 2 := by
      rw [sq_abs]; ring
    have a2 : (rhoC p u - u).im * (rhoC p u - u).im = |(rhoC p u - u).im| ^ 2 := by
      rw [sq_abs]; ring
    rw [a1, a2]
    have b1 : |(rhoC p u - u).re| ^ 2 < (1 / 2 ^ p) ^ 2 :=
      pow_lt_pow_left₀ hre (abs_nonneg _) two_ne_zero
    have b2 : |(rhoC p u - u).im| ^ 2 < (1 / 2 ^ p) ^ 2 :=
      pow_lt_pow_left₀ him (abs_nonneg _) two_ne_zero
    have : (1 / (2 : ℝ) ^ p) ^ 2 = 1 / (2 ^ p) ^ 2 := by rw [div_pow, one_pow]
    rw [this] at b1 b2
    have : (2 : ℝ) / (2 ^ p) ^ 2 = 1 / (2 ^ p) ^ 2 + 1 / (2 ^ p) ^ 2 := by ring
    rw [this]
    exact add_lt_add b1 b2
  calc √((rhoC p u - u).re * (rhoC p u - u).re + (rhoC p u - u).im * (rhoC p u - u).im)
      < √(2 / (2 ^ p) ^ 2) := by
        exact Real.sqrt_lt_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) hbound
    _ = Real.sqrt 2 / 2 ^ p := by
        rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hp.le]

theorem norm_rhoC_sub_le_two (p : ℕ) (u : ℂ) : ‖rhoC p u - u‖ ≤ 2 / 2 ^ p := by
  have h := norm_rhoC_sub_lt p u
  have hs : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  calc ‖rhoC p u - u‖ ≤ Real.sqrt 2 / 2 ^ p := h.le
    _ ≤ 2 / 2 ^ p := div_le_div_of_nonneg_right hs hp.le

section Linear

variable {V W X : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The scaled error `2^p ‖v' - v‖` of approximating `v` by `v'`. -/
noncomputable def errVec (p : ℕ) (v' v : V) : ℝ := 2 ^ p * ‖v' - v‖

/-- `A'` approximates the contraction `A` on the unit ball with scaled error at most `ε`. -/
def ApproxMap (p : ℕ) (A' : V → W) (A : V →L[ℂ] W) (ε : ℝ) : Prop :=
  ∀ v, ‖v‖ ≤ 1 → 2 ^ p * ‖A' v - A v‖ ≤ ε

/-- Lemma 2.7: errors add when an approximate contraction meets an approximate input. -/
theorem approx_apply {p : ℕ} {A' : V → W} {A : V →L[ℂ] W} {ε η : ℝ} {v' v : V}
    (hA : ‖A‖ ≤ 1) (hA' : ApproxMap p A' A ε) (hv : ‖v'‖ ≤ 1)
    (hvv : 2 ^ p * ‖v' - v‖ ≤ η) : 2 ^ p * ‖A' v' - A v‖ ≤ ε + η := by
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  have h1 := hA' v' hv
  have h2 : ‖A v' - A v‖ ≤ ‖v' - v‖ := by
    rw [← map_sub]
    calc ‖A (v' - v)‖ ≤ ‖A‖ * ‖v' - v‖ := A.le_opNorm _
      _ ≤ 1 * ‖v' - v‖ := by gcongr
      _ = ‖v' - v‖ := one_mul _
  have h3 : ‖A' v' - A v‖ ≤ ‖A' v' - A v'‖ + ‖A v' - A v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  calc 2 ^ p * ‖A' v' - A v‖ ≤ 2 ^ p * (‖A' v' - A v'‖ + ‖A v' - A v‖) := by gcongr
    _ = 2 ^ p * ‖A' v' - A v'‖ + 2 ^ p * ‖A v' - A v‖ := by ring
    _ ≤ ε + η := by
        apply add_le_add h1
        calc 2 ^ p * ‖A v' - A v‖ ≤ 2 ^ p * ‖v' - v‖ := by gcongr
          _ ≤ η := hvv

/-- Corollary 2.8: composing approximations adds their errors. -/
theorem approx_comp {p : ℕ} {A' : V → W} {A : V →L[ℂ] W} {B' : W → X} {B : W →L[ℂ] X}
    {ε₁ ε₂ : ℝ} (hB : ‖B‖ ≤ 1)
    (hA' : ApproxMap p A' A ε₁) (hB' : ApproxMap p B' B ε₂)
    (hA'ball : ∀ u, ‖u‖ ≤ 1 → ‖A' u‖ ≤ 1) :
    ApproxMap p (B' ∘ A') (B ∘L A) (ε₂ + ε₁) := by
  intro u hu
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  exact approx_apply hB hB' (hA'ball u hu) (hA' u hu)

/-- `A'` approximates the bilinear contraction `A` on unit balls with scaled error at most `ε`. -/
def ApproxBil (p : ℕ) (A' : V → W → X) (A : V →L[ℂ] W →L[ℂ] X) (ε : ℝ) : Prop :=
  ∀ u v, ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → 2 ^ p * ‖A' u v - A u v‖ ≤ ε

/-- Lemma 2.9: bilinear error propagation. -/
theorem approx_bil_apply {p : ℕ} {A' : V → W → X} {A : V →L[ℂ] W →L[ℂ] X} {ε η₁ η₂ : ℝ}
    {u' u : V} {v' v : W}
    (hA : ‖A‖ ≤ 1) (hA' : ApproxBil p A' A ε) (hu' : ‖u'‖ ≤ 1) (hv' : ‖v'‖ ≤ 1)
    (hu : ‖u‖ ≤ 1) (huu : 2 ^ p * ‖u' - u‖ ≤ η₁) (hvv : 2 ^ p * ‖v' - v‖ ≤ η₂) :
    2 ^ p * ‖A' u' v' - A u v‖ ≤ ε + η₁ + η₂ := by
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  have h1 := hA' u' v' hu' hv'
  have h2 : ‖A u' v' - A u v'‖ ≤ ‖u' - u‖ := by
    have e : A u' v' - A u v' = A (u' - u) v' := by simp [map_sub]
    rw [e]
    calc ‖A (u' - u) v'‖ ≤ ‖A‖ * ‖u' - u‖ * ‖v'‖ := A.le_opNorm₂ _ _
      _ ≤ 1 * ‖u' - u‖ * 1 := by gcongr
      _ = ‖u' - u‖ := by ring
  have h3 : ‖A u v' - A u v‖ ≤ ‖v' - v‖ := by
    rw [← map_sub]
    calc ‖A u (v' - v)‖ ≤ ‖A‖ * ‖u‖ * ‖v' - v‖ := A.le_opNorm₂ _ _
      _ ≤ 1 * 1 * ‖v' - v‖ := by gcongr
      _ = ‖v' - v‖ := by ring
  have h4 : ‖A' u' v' - A u v‖ ≤ ‖A' u' v' - A u' v'‖ + ‖A u' v' - A u v'‖ + ‖A u v' - A u v‖ := by
    calc ‖A' u' v' - A u v‖ ≤ ‖A' u' v' - A u v'‖ + ‖A u v' - A u v‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖A' u' v' - A u' v'‖ + ‖A u' v' - A u v'‖ + ‖A u v' - A u v‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub (A' u' v') (A u' v') (A u v')
          linarith
  calc 2 ^ p * ‖A' u' v' - A u v‖
      ≤ 2 ^ p * (‖A' u' v' - A u' v'‖ + ‖A u' v' - A u v'‖ + ‖A u v' - A u v‖) := by gcongr
    _ = 2 ^ p * ‖A' u' v' - A u' v'‖ + 2 ^ p * ‖A u' v' - A u v'‖
        + 2 ^ p * ‖A u v' - A u v‖ := by ring
    _ ≤ ε + η₁ + η₂ := by
        gcongr
        · calc 2 ^ p * ‖A u' v' - A u v'‖ ≤ 2 ^ p * ‖u' - u‖ := by gcongr
            _ ≤ η₁ := huu
        · calc 2 ^ p * ‖A u v' - A u v‖ ≤ 2 ^ p * ‖v' - v‖ := by gcongr
            _ ≤ η₂ := hvv

end Linear

/-- Rounded complex multiplication approximates the multiplication map with error `2`. -/
theorem approxBil_mul_rhoC (p : ℕ) :
    ApproxBil p (fun u v => rhoC p (u * v)) (ContinuousLinearMap.mul ℂ ℂ) 2 := by
  intro u v _ _
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  simp only [ContinuousLinearMap.mul_apply']
  have := norm_rhoC_sub_le_two p (u * v)
  calc 2 ^ p * ‖rhoC p (u * v) - u * v‖ ≤ 2 ^ p * (2 / 2 ^ p) := by gcongr
    _ = 2 := by field_simp

/-- Corollary 2.10: a rounded product of approximate unit-ball inputs errs by at most `2`
more than the inputs. -/
theorem approx_mul_round {p : ℕ} {η₁ η₂ : ℝ} {u' u v' v : ℂ}
    (hu' : ‖u'‖ ≤ 1) (hv' : ‖v'‖ ≤ 1) (hu : ‖u‖ ≤ 1)
    (huu : 2 ^ p * ‖u' - u‖ ≤ η₁) (hvv : 2 ^ p * ‖v' - v‖ ≤ η₂) :
    2 ^ p * ‖rhoC p (u' * v') - u * v‖ ≤ 2 + η₁ + η₂ := by
  have h := approx_bil_apply (A := ContinuousLinearMap.mul ℂ ℂ)
    (A' := fun u v => rhoC p (u * v)) (ContinuousLinearMap.opNorm_mul_le ℂ ℂ)
    (approxBil_mul_rhoC p) hu' hv' hu huu hvv
  simpa only [ContinuousLinearMap.mul_apply'] using h

section Slice

variable {m n : ℕ} {β : Type*} [Fintype β]

/-- Apply a map on `Fin m → ℂ` to every `β`-slice of `Fin m × β → ℂ`. -/
def sliceMap (A : (Fin m → ℂ) → (Fin n → ℂ)) : (Fin m × β → ℂ) → (Fin n × β → ℂ) :=
  fun u jb => A (fun i => u (i, jb.2)) jb.1

/-- Restriction to one `β`-slice, as a continuous linear map. -/
noncomputable def restrictSlice (b : β) : (Fin m × β → ℂ) →L[ℂ] (Fin m → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (i, b)

/-- The slice-wise action of a continuous linear map, as a continuous linear map. -/
noncomputable def sliceCLM (A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) :
    (Fin m × β → ℂ) →L[ℂ] (Fin n × β → ℂ) :=
  ContinuousLinearMap.pi fun jb =>
    (ContinuousLinearMap.proj jb.1).comp (A.comp (restrictSlice jb.2))

omit [Fintype β] in
theorem sliceCLM_apply (A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) (u : Fin m × β → ℂ) :
    sliceCLM A u = sliceMap A u := by
  funext jb
  simp [sliceCLM, restrictSlice, sliceMap]

theorem norm_slice_le (u : Fin m × β → ℂ) (b : β) : ‖fun i => u (i, b)‖ ≤ ‖u‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  exact norm_le_pi_norm u (i, b)

theorem norm_sliceMap_le (A : (Fin m → ℂ) → (Fin n → ℂ)) (u : Fin m × β → ℂ) {M : ℝ}
    (hM : 0 ≤ M) (hA : ∀ b : β, ‖A (fun i => u (i, b))‖ ≤ M) :
    ‖sliceMap A u‖ ≤ M := by
  rw [pi_norm_le_iff_of_nonneg hM]
  intro jb
  calc ‖sliceMap A u jb‖ = ‖A (fun i => u (i, jb.2)) jb.1‖ := rfl
    _ ≤ ‖A (fun i => u (i, jb.2))‖ := norm_le_pi_norm _ _
    _ ≤ M := hA jb.2

theorem opNorm_sliceCLM_le (A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) (hA : ‖A‖ ≤ 1) :
    ‖sliceCLM (β := β) A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [sliceCLM_apply, one_mul]
  apply norm_sliceMap_le _ _ (norm_nonneg _)
  intro b
  calc ‖A (fun i => u (i, b))‖ ≤ ‖A‖ * ‖fun i => u (i, b)‖ := A.le_opNorm _
    _ ≤ 1 * ‖u‖ := by gcongr; exact norm_slice_le u b
    _ = ‖u‖ := one_mul _

/-- The one-coordinate case of Lemma 2.11: applying an approximation to every slice
keeps its error bound. -/
theorem approxMap_sliceMap {p : ℕ} {A' : (Fin m → ℂ) → (Fin n → ℂ)}
    {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} {ε : ℝ} (hA' : ApproxMap p A' A ε) :
    ApproxMap p (sliceMap (β := β) A') (sliceCLM A) ε := by
  intro u hu
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  have hε : 0 ≤ ε := by
    have := hA' 0 (by simp)
    exact le_trans (by positivity) this
  rw [sliceCLM_apply]
  have : ‖sliceMap A' u - sliceMap A u‖ ≤ ε / 2 ^ p := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro jb
    have h := hA' (fun i => u (i, jb.2)) (le_trans (norm_slice_le u jb.2) hu)
    calc ‖(sliceMap A' u - sliceMap A u) jb‖
        = ‖(A' (fun i => u (i, jb.2)) - A (fun i => u (i, jb.2))) jb.1‖ := rfl
      _ ≤ ‖A' (fun i => u (i, jb.2)) - A (fun i => u (i, jb.2))‖ := norm_le_pi_norm _ _
      _ ≤ ε / 2 ^ p := by
          rw [le_div_iff₀ (by positivity)]
          linarith
  calc 2 ^ p * ‖sliceMap A' u - sliceMap A u‖ ≤ 2 ^ p * (ε / 2 ^ p) := by gcongr
    _ = ε := by field_simp

/-- Slices of unit-ball inputs stay in the unit ball under a unit-ball-preserving map. -/
theorem sliceMap_ball {A' : (Fin m → ℂ) → (Fin n → ℂ)}
    (hA'ball : ∀ v, ‖v‖ ≤ 1 → ‖A' v‖ ≤ 1) (u : Fin m × β → ℂ) (hu : ‖u‖ ≤ 1) :
    ‖sliceMap (β := β) A' u‖ ≤ 1 :=
  norm_sliceMap_le _ _ zero_le_one fun b => hA'ball _ (le_trans (norm_slice_le u b) hu)

end Slice

end IntegerMultBounds.NLogN
