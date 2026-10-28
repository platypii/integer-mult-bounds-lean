module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComplexB0Endpoint
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedDispatchGrid
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridB0Budget

/-! The restored production dispatcher realizes the normalized operator interface with uniform error ten. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.FastB0
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open ContinuousLinearMap

variable {s t T Q A : ℕ} [NeZero s] [NeZero t] {U : Type}

noncomputable def executedDispatchGridInverse (work : Fin 303 → Fin T)
    (src saved count tmp spare result clock savedClock : Fin T) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (p u l target t : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (F : ZMod s → GaussianInt) : ZMod s → ℂ :=
  pairedCellRead p (2*p+13) (cstream A (2*p+13)
    (chirpLine s (executedDispatchGridOutput work src saved count tmp spare result clock savedClock
      recovery hR hQ p u l target t v S F)))

theorem executed_dispatch_resampB₀_spec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (familyInverseCoreReg i)) = [])
    (hcontrol : ∀ k ∈ [count,tmp,spare,result,saved,savedClock], S.R k = [])
    (hst : s < t) {α d : ℝ} (hα : 0 < α) (p u l target : ℕ) (hp : 4 ≤ p) (htarget : p+8 ≤ target)
    (hwidth : 8*p ≤ 2^u) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (hJ : J ∘L PhaseCellOperator.exact s t α = 1)
    (df : ZMod s → ℝ) (hdf : ∀ i, 2^p*‖rhoC p (df i : ℂ)-(dPrime s t α i : ℂ)‖ ≤ 2)
    (hdf1 : ∀ i, ‖rhoC p (df i : ℂ)‖ ≤ 1) :
    ApproxMap p (resampB₀Of (t := t) p
      (fun z => executedDispatchGridInverse work src saved count tmp spare result clock savedClock recovery hR hQ p u l target t v S (gridInput p z)) df)
      (((2 : ℂ)^inverseNormalizationShift p)⁻¹ • resampB₀ s t α J)
      10 ∧
      ∀ w : ZMod t → ℂ, ‖w‖ ≤ 1 → ‖resampB₀Of (t := t) p
        (fun z => executedDispatchGridInverse work src saved count tmp spare result clock savedClock recovery hR hQ p u l target t v S (gridInput p z)) df w‖ ≤ 1 := by
  let compute : (ZMod s → GaussianInt) → ZMod s → ℂ := executedDispatchGridInverse work src saved count tmp spare result clock savedClock recovery hR hQ p u l target t v S
  have hsolve : ∀ F : ZMod s → GaussianInt, (∀ i, ‖value p (F i)‖ ≤ 1) → ∀ yr yi : ZMod s → ℝ,
      Matrix.mulVec (PhaseCellMatrix.realMatrix s t p u) yr = (fun i => ((1/2 : ℂ)*value p (F i)).re) →
      Matrix.mulVec (PhaseCellMatrix.realMatrix s t p u) yi = (fun i => ((1/2 : ℂ)*value p (F i)).im) →
      ∀ i, ‖compute F i-((2 : ℂ)^inverseNormalizationShift p)⁻¹*(⟨yr i,yi i⟩ : ℂ)‖ ≤
        2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p := by
    intro F hF yr yi hyr hyi
    obtain ⟨v',n,huser,hcost,he,herror⟩ := executedDispatchGrid_spec work hwork src saved count tmp spare result clock savedClock hreg hsep recovery hR hQ hA
      (by omega : 2 ≤ p) hwidth hα hst hu hαu hθ hgap hbudget hband hpad F hF v S hblank hleft hcontrol yr yi hyr hyi
    exact herror
  obtain ⟨hmap,hball⟩ := concrete_resampB₀_specGrid hst hα p u (inverseNormalizationShift p) (by omega) hwidth hαu hθ hgap hbudget
    (inverseNormalizationShift_large p) compute _ (by positivity) hsolve
    (gridInverse_normalized_smallness hp htarget) J hJ df hdf hdf1
  exact ⟨fun w hw => (hmap w hw).trans (gridInverse_operator_error_le_ten hp htarget),hball⟩

end IntegerMultBounds.MathlibTM2.Mult.FastB0
