module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowValue

/-! Consume one RHS, publish its residual/recovery result and advance the coordinate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def couplingRowStep (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 117 Q A U :=
  .seq (rawCouplingRow hQ boundary)
    (.seq (discardPrefix 94 93 104 105) (.act (.push (.rt 107) (fun _ => tick) .done)))

def couplingRowStepCost (P q w s t u band a b i : ℕ) : ℕ :=
  rawCouplingRowCost P q w s t u band a b i+6*w+7

theorem couplingRowStep_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (rhs : GaussianInt) (tail rhsTail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail) S)
    (hindex : (S.R 107).length = i) (hrhs : S.R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ couplingRowStepCost P q w s t u band a b i ∧
      Exec body (couplingRowStep hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          113 (csyms A w (couplingRowWord P q t u band a b i boundary C rhs)++S.R 113))
          93 rhsTail) 107 (tick::S.R 107))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := rawCouplingRow_exec (body := body) hQ boundary hA hw5 hqw
    hst haS hbS hbandS hi hP C tail v S hready.precision hready.fraction hready.parameter
    hready.axis hready.period hready.bandwidth hindex (hready.fresh 105 (by simp))
    hready.lower hready.upper hready.width (hready.fresh 115 (by simp)) (hready.fresh 104 (by simp))
    (hready.fresh 109 (by simp)) (hready.fresh 106 (by simp)) (hready.fresh 108 (by simp))
    hready.low hready.source (hready.fresh 92 (by simp)) (hready.fresh 116 (by simp))
    (hready.fresh 102 (by simp)) rhs rhsTail hrhs hready.clean hready.arithmetic hready.left
    (hready.fresh 96 (by simp)) hxs has
  let z := couplingRowWord P q t u band a b i boundary C rhs
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 113 (csyms A w z++S.R 113)}
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := 94) (src := 93) (trash := 104) (tmp := 105) (by decide)
    (csyms A w rhs) rhsTail v₁ S₁ (by simpa [S₁] using hrhs)
    (by simp [S₁,hready.width])
    (by simpa [S₁] using hready.fresh 104 (by simp))
    (by simpa [S₁] using hready.fresh 105 (by simp))
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 93 rhsTail}
  have he₃ : Exec body (.act (.push (.rt 107) (fun _ => tick) .done)) (mk v₂ S₂) 1
      (mk v₂ {S₂ with R := Function.update S₂.R 107 (tick::S₂.R 107)}) := by
    simpa [Action.run,update_rt] using Exec.act (body := body) (.push (.rt 107) (fun _ => tick) .done) (mk v₂ S₂)
  refine ⟨v₂,m₁+((6*w+6)+1),hu₂.trans hu₁,by dsimp only [couplingRowStepCost]; omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by simp) ?_⟩
  apply congrArg (mk v₂)
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
