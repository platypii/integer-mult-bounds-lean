module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexB0Endpoint
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridB0Budget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalGridInput

/-! Every returned full-line production result keeps the unit ball and approximates the exact inverse. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.FastB0
open ContinuousLinearMap Finset

variable {s t A : ℕ} [NeZero s] [NeZero t]

def NormalizedOperatorApprox (p : ℕ) (r : FamilyDispatchInput s A)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (Zs : List (ZMod s → GaussianInt)) : Prop :=
  List.Forall₂ (fun F Z =>
    let out : ZMod s → ℂ := pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s Z))
    ‖out‖ ≤ 1 ∧ 2^p*‖out-(((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J)
      ((1/2 : ℂ) • fun i => value p (F i))‖ ≤ 3) r.inputs Zs

theorem normalizedDispatchApprox_full_operator {p l : ℕ} {d : ℝ} (hp : 4 ≤ p) (hst : s < t)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (r : FamilyDispatchInput s A) (hr : GridDispatchReady p l t d r)
    (ha : r.a = 0) (hb : r.b = s) (htarget : p+8 ≤ r.target)
    (x y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hx : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b) (x F)
      (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hy : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b) (y F)
      (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s t (Real.sqrt (r.u : ℝ)) = 1)
    (Zs : List (ZMod s → GaussianInt)) (happrox : NormalizedDispatchApprox p r x y Zs) :
    NormalizedOperatorApprox p r J Zs := by
  have hαu : (Real.sqrt (r.u : ℝ))^2 = (r.u : ℝ) := Real.sq_sqrt (by positivity)
  have hα : 0 < Real.sqrt (r.u : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr.uPositive)
  obtain ⟨L,hJn,hLH,hdiff⟩ := rounded_inverse_endpoint hst hα p r.u (by omega) hr.width hαu hθ hgap
    (by rw [hαu]; exact hr.budget) J hJ
  have hfull : haloVertices s r.a r.b = univ := by rw [ha,hb,haloVertices_full]
  let R := fun F Z => PhaseCellInterface.ErrorOn (haloVertices s r.a r.b)
    (pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s Z)))
    (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(⟨x F i,y F i⟩ : ℂ))
    (2/(2 : ℝ)^p+(1/(2 : ℝ)^r.target)/(2 : ℝ)^inverseNormalizationShift p)
  have hm : List.Forall₂ (fun F Z => F ∈ r.inputs ∧ R F Z) r.inputs Zs :=
    (List.forall₂_and_left r.inputs Zs).mpr ⟨fun _ h => h,happrox⟩
  apply List.Forall₂.imp _ hm
  intro F Z hpair
  obtain ⟨hFmem,herror⟩ := hpair
  let v := fun i => value p (F i)
  let out : ZMod s → ℂ := pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s Z))
  have hv : ‖v‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr (hr.inputBound F hFmem)
  have hyr : Matrix.mulVec (realMatrix s t p r.u) (x F) = (fun i => ((1/2 : ℂ)*v i).re) := by
    funext i
    simpa only [hfull,Matrix.mulVec,dotProduct] using hx F hFmem i (by rw [hfull]; exact mem_univ i)
  have hyi : Matrix.mulVec (realMatrix s t p r.u) (y F) = (fun i => ((1/2 : ℂ)*v i).im) := by
    funext i
    simpa only [hfull,Matrix.mulVec,dotProduct] using hy F hFmem i (by rw [hfull]; exact mem_univ i)
  have hLv := inverse_parts p r.u L hLH ((1/2 : ℂ) • v) (x F) (y F)
    (by rw [hyr]; rfl) (by rw [hyi]; rfl)
  have he : ‖out-((2 : ℂ)^inverseNormalizationShift p)⁻¹ • L ((1/2 : ℂ) • v)‖ ≤
      2/(2 : ℝ)^p+(1/(2 : ℝ)^r.target)/(2 : ℝ)^inverseNormalizationShift p := by
    rw [hLv,pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    exact herror i (by rw [hfull]; exact mem_univ i)
  have hs := smallgap_inverse_value_spec p (inverseNormalizationShift p) J L hJn (inverseNormalizationShift_large p)
    hdiff (gridInverse_normalized_smallness hp htarget) v out hv he
  have hbound := gridInverse_operator_error_le_ten (j := inverseNormalizationShift p) hp htarget
  exact ⟨hs.1,hs.2.trans (by linarith only [hbound])⟩

def NormalizedOperatorProduced (p : ℕ)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (r : FamilyDispatchInput s A) (output : List (Fin (A+4))) : Prop :=
  ∃ Zs, output = r.normalizedOutput p Zs ∧ NormalizedOperatorApprox p r (J r) Zs

theorem normalizedDispatchProduced_full_operator {p l : ℕ} {d : ℝ} (hp : 4 ≤ p) (hst : s < t)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (records : List (FamilyDispatchInput s A)) (hready : ∀ r ∈ records, GridDispatchReady p l t d r)
    (hfull : ∀ r ∈ records, r.a = 0 ∧ r.b = s) (htarget : ∀ r ∈ records, p+8 ≤ r.target)
    (x y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hx : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (x r F) (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hy : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (y r F) (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : ∀ r ∈ records, J r ∘L PhaseCellOperator.exact s t (Real.sqrt (r.u : ℝ)) = 1)
    (outputs : List (List (Fin (A+4)))) (happrox : List.Forall₂ (NormalizedDispatchProduced p x y) records outputs) :
    List.Forall₂ (NormalizedOperatorProduced p J) records outputs := by
  have hm : List.Forall₂ (fun r output => r ∈ records ∧ NormalizedDispatchProduced p x y r output) records outputs :=
    (List.forall₂_and_left records outputs).mpr ⟨fun _ h => h,happrox⟩
  apply List.Forall₂.imp _ hm
  intro r output hpair
  obtain ⟨hr,Zs,hZ,ha⟩ := hpair
  exact ⟨Zs,hZ,normalizedDispatchApprox_full_operator hp hst hθ hgap r (hready r hr)
    (hfull r hr).1 (hfull r hr).2 (htarget r hr) (x r) (y r) (hx r hr) (hy r hr) (J r) (hJ r hr) Zs ha⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
