module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchCoreTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexB0Endpoint
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridB0Budget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPublishedOperator
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedInverseTransfer

/-! The same fields returned by production dispatch approximate the exact
inverse on their generated core. Precision discharges the perturbation budget. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface IntegerMultBounds.MathlibTM2.Mult.FastB0
variable {s A : ℕ} [NeZero s]

theorem GeneratedCoreProduced.exact_inverse {p l t width : ℕ} [NeZero t] {d : ℝ}
    (hp : 4 ≤ p) (hst : s < t) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (r : FamilyDispatchInput s A) (hr : GridDispatchReady p l t d r) (htarget : p+2 ≤ r.target)
    (k : FamilyDispatchInput s A → ℕ)
    (X Y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hX : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) Finset.univ (X r F)
      (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hY : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) Finset.univ (Y r F)
      (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s t (Real.sqrt (r.u : ℝ)) = 1)
    (output : List (Fin (A+4))) (hproduced : GeneratedCoreProduced p width r.target k X Y r output) :
    ∃ Zs, output = r.normalizedOutput p Zs ∧
      List.Forall₂ (fun F Z =>
        let out := pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s Z))
        (∀ i ∈ ownedCore s width (k r), ‖out i‖ ≤ 1) ∧
        ErrorOn (ownedCore s width (k r)) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J) ((1/2 : ℂ) • fun i => value p (F i)))
          (3/(2 : ℝ)^p)) r.inputs Zs := by
  have hα : 0 < Real.sqrt (r.u : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr.uPositive)
  have hαu : (Real.sqrt (r.u : ℝ))^2 = (r.u : ℝ) := Real.sq_sqrt (by positivity)
  obtain ⟨L,hJn,hLH,hdiff⟩ := rounded_inverse_endpoint hst hα p r.u (by omega) hr.width hαu hθ hgap
    (by rw [hαu]; exact hr.budget) J hJ
  let j := inverseNormalizationShift p
  let e := (2/(2 : ℝ)^p+(1/(2 : ℝ)^r.target)/(2 : ℝ)^j)+
    (1/(2 : ℝ)^r.target+1/(2 : ℝ)^r.target)/(2 : ℝ)^j
  let δ := 32*(p : ℝ)^2/(2 : ℝ)^(45*p)
  have hcore : e ≤ (11/4 : ℝ)/(2 : ℝ)^p := generatedCore_error_le_quarters htarget
  have hscaled : (2 : ℝ)^p*(e+δ/2) ≤ 3 := by
    have he := (le_div_iff₀ (by positivity : (0 : ℝ) < 2^p)).mp hcore
    have hm := gridInverse_matrix_error_le_quarter hp
    change (2 : ℝ)^p*(δ/2) ≤ 1/4 at hm
    nlinarith only [he,hm]
  have htotal : e+δ/2 ≤ 3/(2 : ℝ)^p :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 2^p)).mpr (by nlinarith only [hscaled])
  have hsmall : e+δ/2 ≤ 1/2 := htotal.trans (publishedInverse_smallness hp)
  obtain ⟨Zs,houtput,hgood⟩ := hproduced
  refine ⟨Zs,houtput,?_⟩
  have hm := (List.forall₂_and_left r.inputs Zs).mpr ⟨fun _ hF => hF,hgood⟩
  apply List.Forall₂.imp _ hm
  intro F Z hpair
  obtain ⟨hF,herror⟩ := hpair
  let v := fun i => value p (F i)
  have hv : ‖v‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr (hr.inputBound F hF)
  have hLv := inverse_parts p r.u L hLH ((1/2 : ℂ) • v) (X r F) (Y r F)
    (by funext i; simpa [Matrix.mulVec,dotProduct] using hX F hF i (Finset.mem_univ i))
    (by funext i; simpa [Matrix.mulVec,dotProduct] using hY F hF i (Finset.mem_univ i))
  have he : ErrorOn (ownedCore s width (k r))
      (pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s Z)))
      (((2 : ℂ)^j)⁻¹ • L ((1/2 : ℂ) • v)) e := by
    intro i hi
    simpa only [hLv,Pi.smul_apply,smul_eq_mul] using herror i hi
  obtain ⟨hball,htransfer⟩ := inverse_core_value_spec p j J L hJn (inverseNormalizationShift_large p)
    e δ (by positivity) hdiff hsmall (ownedCore s width (k r)) v _ hv he
  refine ⟨hball,?_⟩
  intro i hi
  exact (htransfer i hi).trans htotal

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
