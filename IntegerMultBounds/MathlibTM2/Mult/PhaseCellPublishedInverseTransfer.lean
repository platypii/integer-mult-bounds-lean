module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowAssembly
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellB0

/-! Transfer rounded-inverse core certificates to the exact inverse. Filling
outside the core permits reuse of the established whole-vector comparison. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.FastB0
variable {s : ℕ} [NeZero s]

theorem inverse_core_value_spec (p j : ℕ)
    (J L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJn : ‖J‖ ≤ 4*(p : ℝ)) (hj : 4*(p : ℝ) ≤ 2^j)
    (e δ : ℝ) (he : 0 ≤ e) (hdiff : ‖L-J‖ ≤ δ) (hsmall : e+δ/2 ≤ 1/2)
    (core : Finset (ZMod s)) (v out : ZMod s → ℂ) (hv : ‖v‖ ≤ 1)
    (herror : ErrorOn core out (((2 : ℂ)^j)⁻¹ • L ((1/2 : ℂ) • v)) e) :
    (∀ i ∈ core, ‖out i‖ ≤ 1) ∧
      ErrorOn core out ((((2 : ℂ)^j)⁻¹ • J) ((1/2 : ℂ) • v)) (e+δ/2) := by
  let completed := fun i => if i ∈ core then out i else (((2 : ℂ)^j)⁻¹ • L ((1/2 : ℂ) • v)) i
  have hc : ‖completed-((2 : ℂ)^j)⁻¹ • L ((1/2 : ℂ) • v)‖ ≤ e := by
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    by_cases hi : i ∈ core
    · simpa only [Pi.sub_apply,completed,ite_eq_left hi] using herror i hi
    · simpa only [Pi.sub_apply,completed,ite_eq_right hi,sub_self,norm_zero] using he
  obtain ⟨hball,hscaled⟩ := smallgap_inverse_value_spec p j J L hJn hj hdiff hsmall v completed hv hc
  have hglobal : ‖completed-(((2 : ℂ)^j)⁻¹ • J) ((1/2 : ℂ) • v)‖ ≤ e+δ/2 :=
    (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2^p)).mp hscaled
  constructor
  · intro i hi
    simpa only [completed,ite_eq_left hi] using (norm_le_pi_norm completed i).trans hball
  · intro i hi
    have h := (norm_le_pi_norm (completed-(((2 : ℂ)^j)⁻¹ • J) ((1/2 : ℂ) • v)) i).trans hglobal
    simpa only [Pi.sub_apply,completed,ite_eq_left hi] using h

/-- A covered publication of rounded-system results supplies the exact-inverse
operator contract and keeps the unit ball. Locality is included in `e` once. -/
theorem publishedWindows_inverse_spec (p j : ℕ)
    (J L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJn : ‖J‖ ≤ 4*(p : ℝ)) (hj : 4*(p : ℝ) ≤ 2^j)
    (e δ : ℝ) (he : 0 ≤ e) (hdiff : ‖L-J‖ ≤ δ) (hsmall : e+δ/2 ≤ 1/2)
    (ws : List (Window (ZMod s)))
    (localOut : Window (ZMod s) → (ZMod s → ℂ) → ZMod s → ℂ)
    (initial : (ZMod s → ℂ) → ZMod s → ℂ)
    (hcover : ∀ i, ∃ w ∈ ws, i ∈ w.core)
    (hlocal : ∀ w ∈ ws, ∀ v, ‖v‖ ≤ 1 →
      ErrorOn w.core (localOut w v) (((2 : ℂ)^j)⁻¹ • L ((1/2 : ℂ) • v)) e) :
    ApproxMap p (fun v => publishWindows (fun w => localOut w v) ws (initial v))
      (((2 : ℂ)^j)⁻¹ • ((1/2 : ℂ) • J)) ((2 : ℝ)^p*(e+δ/2)) ∧
      ∀ v, ‖v‖ ≤ 1 → ‖publishWindows (fun w => localOut w v) ws (initial v)‖ ≤ 1 := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hdiff
  have hcore (w) (hw : w ∈ ws) (v) (hv : ‖v‖ ≤ 1) :=
    inverse_core_value_spec p j J L hJn hj e δ he hdiff hsmall w.core v (localOut w v) hv (hlocal w hw v hv)
  constructor
  · intro v hv
    have herr := norm_error_of_publish ws (fun w => localOut w v)
      (publishWindows (fun w => localOut w v) ws (initial v))
      ((((2 : ℂ)^j)⁻¹ • J) ((1/2 : ℂ) • v)) (e+δ/2) (by positivity)
      (fun w hw => (hcore w hw v hv).2)
      (fun i => publishWindows_source (fun w => localOut w v) ws (initial v) i (hcover i))
    have htarget : (((2 : ℂ)^j)⁻¹ • ((1/2 : ℂ) • J)) v =
        (((2 : ℂ)^j)⁻¹ • J) ((1/2 : ℂ) • v) := by
      simp only [smul_apply,ContinuousLinearMap.map_smul]
    rw [htarget]
    exact mul_le_mul_of_nonneg_left herr (by positivity)
  · intro v hv
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    obtain ⟨w,hw,hi,hvalue⟩ := publishWindows_source (fun w => localOut w v) ws (initial v) i (hcover i)
    rw [hvalue]
    exact (hcore w hw v hv).1 i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
