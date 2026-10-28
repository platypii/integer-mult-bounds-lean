module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalInverseExec
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! The computed inverse output is selected from the actual raw machine execution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A s : ℕ} [NeZero s] {U : Type}

def CanonicalInverseResult (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (p u l target t : ℕ) (v : HS 303 Q A U) (F G : ZMod s → GaussianInt) : Prop :=
  ∃ v' n, Exec (fun f : Empty => nomatch f) (familyInverseCaller recovery hR hQ)
    (mk v (canonicalInverseInput p u l target s t F)) n
    (mk v' {canonicalInverseInput p u l target s t F with R :=
      (Function.update (canonicalInverseInput (A := A) p u l target s t F).R 132
        (cstream A (inverseFullInputWidth p u l target s t) (chirpLine s G)))})

noncomputable def executedInverseOutput (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (p u l target t : ℕ) (v : HS 303 Q A U) (F : ZMod s → GaussianInt) : ZMod s → GaussianInt := by
  classical
  exact if h : ∃ G, CanonicalInverseResult recovery hR hQ p u l target t v F G then Classical.choose h else 0

theorem executedInverseOutput_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p u l target t : ℕ} {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (F : ZMod s → GaussianInt) (hF : ∀ i, ‖value (inverseFullInputPrecision p u l target s t) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 303 Q A U) (z : ZMod s → ℂ)
    (hz : Matrix.mulVec (fun i j => (realMatrix s t p u i j : ℂ)) z =
      (fun i => value (inverseFullInputPrecision p u l target s t) (F i))) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ familyInverseCallerCost A (inverseCallerWordWidth p u l target s t) p u l target s t ∧
      Exec (fun f : Empty => nomatch f) (familyInverseCaller recovery hR hQ)
        (mk v (canonicalInverseInput p u l target s t F)) n
        (mk v' {canonicalInverseInput p u l target s t F with R :=
          (Function.update (canonicalInverseInput (A := A) p u l target s t F).R 132
            (cstream A (inverseFullInputWidth p u l target s t)
              (chirpLine s (executedInverseOutput recovery hR hQ p u l target t v F))))}) ∧
      ∀ i, ‖pairedCellRead (inverseFullInputPrecision p u l target s t) (inverseFullInputWidth p u l target s t)
        (cstream A (inverseFullInputWidth p u l target s t)
          (chirpLine s (executedInverseOutput recovery hR hQ p u l target t v F))) i-z i‖ ≤ 1/(2 : ℝ)^target := by
  obtain ⟨vi,n,G,hui,hn,hei,herror⟩ := canonicalInverse_exec (body := fun f : Empty => nomatch f)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband hpad F hF v z hz
  have hex : ∃ G, CanonicalInverseResult recovery hR hQ p u l target t v F G := ⟨G,vi,n,hei⟩
  have hchosen : CanonicalInverseResult recovery hR hQ p u l target t v F
      (executedInverseOutput recovery hR hQ p u l target t v F) := by
    classical
    simpa only [executedInverseOutput,dite_eq_left hex] using Classical.choose_spec hex
  obtain ⟨v',m,he⟩ := hchosen
  have hsame := he.unique hei
  have huser : v'.user = vi.user := congrArg (fun z => z.var.user) hsame.2
  have hout := congrArg (fun z => z.stk (.rt (132 : Fin 303))) hsame.2
  simp only [mk_stk,get_rt,Function.update_self] at hout
  refine ⟨v',m,huser.trans hui,by rw [hsame.1]; exact hn,he,?_⟩
  rw [hout]
  exact herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
