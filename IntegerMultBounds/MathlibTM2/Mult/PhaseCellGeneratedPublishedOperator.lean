module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedOperator
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWindows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundDimensions

/-! Generated core coverage and the selected inverse normalization discharge
the geometric and contraction premises of the published operator endpoint. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s : ℕ} [NeZero s]

/-- The selected normalization and half-sized RHS leave half the unit ball
available for arithmetic, locality and matrix-rounding errors. -/
theorem normalizedInverse_norm_le_half (p : ℕ)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : ‖J‖ ≤ 4*(p : ℝ)) :
    ‖((2 : ℂ)^inverseNormalizationShift p)⁻¹ • ((1/2 : ℂ) • J)‖ ≤ 1/2 := by
  have hlarge := inverseNormalizationShift_large p
  calc
    _ = ‖J‖/(2*(2 : ℝ)^inverseNormalizationShift p) := by
      rw [norm_smul,norm_smul,norm_inv,norm_pow,Complex.norm_ofNat]
      norm_num
      ring
    _ ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hJ,hlarge])

/-- Fixed smallness gate for a scaled line error of three. -/
theorem publishedInverse_smallness {p : ℕ} (hp : 4 ≤ p) : (3 : ℝ)/2^p ≤ 1/2 := by
  have hpow : (16 : ℝ) ≤ 2^p := by
    calc
      (16 : ℝ) = 2^4 := by norm_num
      _ ≤ 2^p := pow_le_pow_right₀ (by norm_num) hp
  exact (div_le_iff₀ (by positivity)).mpr (by linarith)

/-- The normalized arithmetic and two component-locality losses fit within
three units of p-bit error at a linear precision target. -/
theorem generatedCore_error_le {p target j : ℕ} (htarget : p+2 ≤ target) :
    (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^j)+
      (1/(2 : ℝ)^target+1/(2 : ℝ)^target)/(2 : ℝ)^j ≤ 3/(2 : ℝ)^p := by
  have ht : (1 : ℝ)/2^target ≤ (1/(2 : ℝ)^p)/4 := by
    calc
      (1 : ℝ)/2^target ≤ 1/(2 : ℝ)^(p+2) :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) htarget)
      _ = (1/(2 : ℝ)^p)/4 := by rw [pow_add]; norm_num; ring
  have hd : ((1 : ℝ)/2^target)/2^j ≤ (1/(2 : ℝ)^p)/4 :=
    (div_le_self (by positivity) (one_le_pow₀ (by norm_num))).trans ht
  calc
    _ = 2/(2 : ℝ)^p+3*((1/(2 : ℝ)^target)/(2 : ℝ)^j) := by ring
    _ ≤ 2/(2 : ℝ)^p+3*((1/(2 : ℝ)^p)/4) := by linarith
    _ ≤ 3/(2 : ℝ)^p := by
      have h : (0 : ℝ) ≤ 1/(2 : ℝ)^p := by positivity
      calc
        _ = (11/4 : ℝ)*(1/(2 : ℝ)^p) := by ring
        _ ≤ 3*(1/(2 : ℝ)^p) := mul_le_mul_of_nonneg_right (by norm_num) h
        _ = 3/(2 : ℝ)^p := by ring

/-- With the generated cover and selected normalization, the only numerical
premise is core accuracy against the exact inverse on the same input. -/
theorem generatedWindows_normalizedInverse_spec (p u target width : ℕ)
    (hp : 4 ≤ p) (hw : 0 < width)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : ‖J‖ ≤ 4*(p : ℝ))
    (localOut : Window (ZMod s) → (ZMod s → ℂ) → ZMod s → ℂ)
    (initial : (ZMod s → ℂ) → ZMod s → ℂ)
    (hlocal : ∀ w ∈ generatedWindows s width p u target, ∀ v, ‖v‖ ≤ 1 →
      ErrorOn w.core (localOut w v)
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*J ((1/2 : ℂ) • v) i) (3/(2 : ℝ)^p)) :
    ApproxMap p (fun v => publishWindows (fun w => localOut w v)
      (generatedWindows s width p u target) (initial v))
      (((2 : ℂ)^inverseNormalizationShift p)⁻¹ • ((1/2 : ℂ) • J)) 3 ∧
      ∀ v, ‖v‖ ≤ 1 → ‖publishWindows (fun w => localOut w v)
        (generatedWindows s width p u target) (initial v)‖ ≤ 1 := by
  apply publishedWindows_operator_spec p _ _ localOut initial 3 (by norm_num)
    (generatedWindows_cover width p u target hw) ?_ (normalizedInverse_norm_le_half p J hJ)
    (publishedInverse_smallness hp)
  intro w hw v hv i hi
  simpa only [smul_apply,ContinuousLinearMap.map_smul,Pi.smul_apply,
    smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hlocal w hw v hv i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
