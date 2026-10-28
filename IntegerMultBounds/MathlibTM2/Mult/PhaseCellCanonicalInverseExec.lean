module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalInverseInput

/-! Execute the numerical inverse from its constructed ordinary scalar/input bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

theorem canonicalInverse_exec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p u l target s t : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (F : ZMod s → GaussianInt) (hF : ∀ i, ‖value (inverseFullInputPrecision p u l target s t) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 303 Q A U) (z : ZMod s → ℂ)
    (hz : Matrix.mulVec (fun i j => (realMatrix s t p u i j : ℂ)) z =
      (fun i => value (inverseFullInputPrecision p u l target s t) (F i))) :
    ∃ v' n G, v'.user = v.user ∧
      n ≤ familyInverseCallerCost A (inverseCallerWordWidth p u l target s t) p u l target s t ∧
      Exec body (familyInverseCaller recovery hR hQ) (mk v (canonicalInverseInput p u l target s t F)) n
        (mk v' {canonicalInverseInput p u l target s t F with R :=
          (Function.update (canonicalInverseInput (A := A) p u l target s t F).R 132
            (cstream A (inverseFullInputWidth p u l target s t) (chirpLine s G)))}) ∧
      ∀ i, ‖pairedCellRead (inverseFullInputPrecision p u l target s t) (inverseFullInputWidth p u l target s t)
        (cstream A (inverseFullInputWidth p u l target s t) (chirpLine s G)) i-z i‖ ≤ 1/(2 : ℝ)^target := by
  obtain ⟨v',n,G,huser,hcost,he,herror,ht⟩ := familyInverseCaller_spec (body := body)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband hpad F hF
    v (canonicalInverseInput p u l target s t F) []
    (List.replicate (inverseCallerWordWidth p u l target s t) Node.tick) (by simp)
    (canonicalInverseInput_scalars p u l target s t F)
    (fun i => canonicalInverseInput_left p u l target s t F _)
    (fun i hi _ => canonicalInverseInput_core p u l target s t F i hi)
    (by simp only [canonicalInverseInput_source,List.append_nil,inverseFullInputWidth]) z hz
  refine ⟨v',n,G,huser,hcost,?_,?_⟩
  · simpa only [canonicalInverseInput_output,List.append_nil,inverseFullInputWidth] using he
  · simpa only [canonicalInverseInput_output,List.append_nil,inverseFullInputWidth,inverseFullInputPrecision] using herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
