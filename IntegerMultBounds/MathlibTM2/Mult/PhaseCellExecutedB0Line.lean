module

public import IntegerMultBounds.MathlibTM2.Mult.ConcreteB0
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedB0Budget

/-! The normalized inverse interface instantiated by the executed solver, not the reference scalar solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.FastB0
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open ContinuousLinearMap Finset

variable {s t Q A : ℕ} [NeZero s] [NeZero t] {U : Type}

theorem executed_phase_resampB₀_spec
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (v : HS 303 Q A U)
    (hst : s < t) {α d : ℝ} (hα : 0 < α) (p u l j : ℕ) (hp : 4 ≤ p)
    (hwidth : 8*p ≤ 2^u) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hj : 4*(p : ℝ) ≤ 2^j)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α = 1)
    (df : ZMod s → ℝ) (hdf : ∀ i, 2^p*‖rhoC p (df i : ℂ)-(dPrime s t α i : ℂ)‖ ≤ 2)
    (hdf1 : ∀ i, ‖rhoC p (df i : ℂ)‖ ≤ 1) :
    ApproxMap p (resampB₀Of (t := t) p
      (bandJtX (s := s) p j (executedRealInverse recovery hR hQ p u l (p+8+1) t v)) df)
      (((2 : ℂ)^j)⁻¹ • resampB₀ s t α J)
      (6+2^p*((2*(1/(2 : ℝ)^(p+8))+2/2^p)+(32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)) ∧
      ∀ w : ZMod t → ℂ, ‖w‖ ≤ 1 → ‖resampB₀Of (t := t) p
        (bandJtX (s := s) p j (executedRealInverse recovery hR hQ p u l (p+8+1) t v)) df w‖ ≤ 1 := by
  have hs := executedRealInverse_dyadic_spec recovery hR hQ hA (by omega : 2 ≤ p)
    hwidth hα hst hu hαu hθ hgap hbudget hband hpad v (target := p+8)
  exact concrete_resampB₀_specX hst hα p u j (by omega) hwidth hαu hθ hgap hbudget hj _ _
    (by positivity) (fun x b hx hb i => hs.full_error x b hx hb i)
    (executedInverse_normalized_smallness hp) J hJ df hdf hdf1

end IntegerMultBounds.MathlibTM2.Mult.FastB0
