module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterWorkspace

/-! Isolate row arithmetic from the retained outer iteration counter. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def outerCouplingRow (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 144 Q A U :=
  embProg groupReg id (couplingRowStep hQ boundary)

theorem outerCouplingRow_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (rhs : GaussianInt) (tail rhsTail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s C)++tail) (embStk groupReg S))
    (hindex : (S.R 107).length = i) (hrhs : S.R 93 = csyms A w rhs++rhsTail)
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ couplingRowStepCost P q w s t u band a b i ∧
      Exec (embTab groupReg body) (outerCouplingRow hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          113 (csyms A w (couplingRowWord P q t u band a b i boundary C rhs)++S.R 113))
          93 rhsTail) 107 (tick::S.R 107))}) := by
  obtain ⟨v₁,m,hu₁,hm,he₁⟩ := couplingRowStep_exec (body := body) hQ boundary hA hw5 hqw
    hst haS hbS hbandS hi hP C rhs tail rhsTail (embDn groupReg v) (embStk groupReg S)
    hready hindex hrhs hxs has
  have hbody : ∀ p, (embTab groupReg body) (id p) = embProg groupReg id (body p) := fun _ => rfl
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := id) (body' := embTab groupReg body) groupReg_injective hbody he₁ v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let B := embStk groupReg S
  let B₁ : Stacks 117 A := {B with R := (Function.update B.R 113
    (csyms A w (couplingRowWord P q t u band a b i boundary C rhs)++B.R 113))}
  let B₂ : Stacks 117 A := {B₁ with R := Function.update B₁.R 93 rhsTail}
  rw [embOvr_updR groupReg_injective B₂ S 107 (tick::B.R 107),
    embOvr_updR groupReg_injective B₁ S 93 rhsTail,
    embOvr_updR groupReg_injective B S 113
      (csyms A w (couplingRowWord P q t u band a b i boundary C rhs)++B.R 113),embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
