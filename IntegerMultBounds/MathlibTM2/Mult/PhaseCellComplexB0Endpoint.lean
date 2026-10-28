module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridB0Generic
public import IntegerMultBounds.MathlibTM2.Mult.ConcreteB0
public import IntegerMultBounds.MathlibTM2.Mult.BandedB0
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellB0
public import IntegerMultBounds.NLogN.PhaseCellSharpInverse
public import IntegerMultBounds.NLogN.PhaseCellBoundary
public import IntegerMultBounds.NLogN.ToeplitzLocal

/-! The normalized endpoint depends on the returned complex vector's error, not on two independent calls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.FastB0
open IntegerMultBounds IntegerMultBounds.NLogN ContinuousLinearMap Finset
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

variable {s t : ℕ} [NeZero s] [NeZero t]

theorem rounded_inverse_endpoint (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α = 1) :
    ∃ L : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ), ‖J‖ ≤ 4*(p : ℝ) ∧
      L ∘L PhaseCellOperator.rounded s t p u = 1 ∧
      ‖L-J‖ ≤ 32*(p : ℝ)^2/(2 : ℝ)^(45*p) := by
  obtain ⟨J0,L,_,hNJ0,hJ0n,hLH,_,_,hdiff⟩ :=
    PhaseCellDominance.selected_rounded_inverse s t hst hα p u hp hwidth hαu hθ hgap hbudget
  have hJeq : J = J0 := by
    refine ContinuousLinearMap.ext fun x => ?_
    have e1 : PhaseCellOperator.exact s t α (J0 x) = x := by
      simpa using congrArg (fun f : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) => f x) hNJ0
    have e2 : J (PhaseCellOperator.exact s t α (J0 x)) = J0 x := by
      simpa using congrArg (fun f : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) => f (J0 x)) hJ
    rw [←e2,e1]
  subst hJeq
  exact ⟨L,hJ0n,hLH,hdiff⟩

theorem concrete_resampB₀_specGrid (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (p u j : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p) (hj : 4*(p : ℝ) ≤ 2^j)
    (compute : (ZMod s → GaussianInt) → ZMod s → ℂ) (e : ℝ) (he : 0 ≤ e)
    (hsolve : ∀ F : ZMod s → GaussianInt, (∀ i, ‖value p (F i)‖ ≤ 1) → ∀ yr yi : ZMod s → ℝ,
      Matrix.mulVec (PhaseCellMatrix.realMatrix s t p u) yr = (fun i => ((1/2 : ℂ)*value p (F i)).re) →
      Matrix.mulVec (PhaseCellMatrix.realMatrix s t p u) yi = (fun i => ((1/2 : ℂ)*value p (F i)).im) →
      ∀ i, ‖compute F i-((2 : ℂ)^j)⁻¹*(⟨yr i,yi i⟩ : ℂ)‖ ≤ e)
    (hsmall : e+(32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2 ≤ 1/2)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α = 1)
    (df : ZMod s → ℝ) (hdf : ∀ i, 2^p*‖rhoC p (df i : ℂ)-(dPrime s t α i : ℂ)‖ ≤ 2)
    (hdf1 : ∀ i, ‖rhoC p (df i : ℂ)‖ ≤ 1) :
    ApproxMap p (resampB₀Of (t := t) p (fun v => compute (gridInput p v)) df)
      (((2 : ℂ)^j)⁻¹ • resampB₀ s t α J)
      (7+2^p*(e+(32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)) ∧
      ∀ w : ZMod t → ℂ, ‖w‖ ≤ 1 →
        ‖resampB₀Of (t := t) p (fun v => compute (gridInput p v)) df w‖ ≤ 1 := by
  obtain ⟨L,hJn,hLH,hdiff⟩ := rounded_inverse_endpoint hst hα p u hp hwidth hαu hθ hgap hbudget J hJ
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hA := PhaseCellMatrix.matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  obtain ⟨R,hR⟩ := SchurDominance.exists_solver _ _ _ hμ hA
  apply resampB₀Of_grid_spec p j J hJn hj compute _ ?_ df hdf hdf1
  intro F hF
  let v := fun i => value p (F i)
  have hv : ‖v‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr hF
  let yr := R (fun i => ((1/2 : ℂ)*v i).re)
  let yi := R (fun i => ((1/2 : ℂ)*v i).im)
  have hyr : Matrix.mulVec (PhaseCellMatrix.realMatrix s t p u) yr = (fun i => ((1/2 : ℂ)*v i).re) :=
    funext fun i => hR _ i (mem_univ i)
  have hyi : Matrix.mulVec (PhaseCellMatrix.realMatrix s t p u) yi = (fun i => ((1/2 : ℂ)*v i).im) :=
    funext fun i => hR _ i (mem_univ i)
  have hLv := inverse_parts p u L hLH ((1/2 : ℂ) • v) yr yi
    (by rw [hyr]; rfl) (by rw [hyi]; rfl)
  have herror : ‖compute F-((2 : ℂ)^j)⁻¹ • L ((1/2 : ℂ) • v)‖ ≤ e := by
    rw [hLv,pi_norm_le_iff_of_nonneg he]
    intro i
    exact hsolve F hF yr yi hyr hyi i
  exact smallgap_inverse_value_spec p j J L hJn hj hdiff hsmall v (compute F) hv herror

end IntegerMultBounds.MathlibTM2.Mult.FastB0
