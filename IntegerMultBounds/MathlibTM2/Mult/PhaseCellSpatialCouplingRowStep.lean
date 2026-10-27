module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterSpatialCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingCursor
public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedCouplingRow

/-! Execute one spatial row, consume its RHS, advance its source and increment its coordinate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

noncomputable def spatialCouplingRowStep (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq (outerSpatialCouplingRow hQ)
    (.seq (discardPrefix 94 93 104 105)
      (.seq advanceSpatialCouplingCursor (.act (.push (.rt 107) (fun _ => tick) .done))))

def spatialCouplingRowStepCost (P q w s t u band i : ℕ) : ℕ :=
  spatialCouplingRowCost P q w s t u band i+10*w+11

theorem spatialCouplingRowStep_exec (hQ : SS.states ≤ Q) {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hPsrc : ((embStk spatialCouplingReg S).R 114).length = P) (hqsrc : ((embStk spatialCouplingReg S).R 112).length = q) (husrc : ((embStk spatialCouplingReg S).R 99).length = u)
    (hsSrc : ((embStk spatialCouplingReg S).R 97).length = s) (htSrc : ((embStk spatialCouplingReg S).R 98).length = t)
    (hbandSrc : ((embStk spatialCouplingReg S).R 100).length = band) (hiSrc : ((embStk spatialCouplingReg S).R 107).length = i) (h105 : (embStk spatialCouplingReg S).R 105 = [])
    (hwsrc : ((embStk spatialCouplingReg S).R 94).length = w) (h115 : (embStk spatialCouplingReg S).R 115 = []) (h104 : (embStk spatialCouplingReg S).R 104 = [])
    (h109 : (embStk spatialCouplingReg S).R 109 = []) (h106 : (embStk spatialCouplingReg S).R 106 = []) (h108 : (embStk spatialCouplingReg S).R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → (embStk spatialCouplingReg S).R r = [])
    (hsrc : (embStk spatialCouplingReg S).R 92 = cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band).drop i)++tail) (h116 : (embStk spatialCouplingReg S).R 116 = []) (h102 : (embStk spatialCouplingReg S).R 102 = [])
    (rhs : GaussianInt) (rhsTail : List (Fin (A+4)))
    (hrhs : (embStk spatialCouplingReg S).R 93 = csyms A w rhs++rhsTail) (hc : CClean mul (embStk spatialCouplingReg S))
    (hcr : ∀ r : CR, (embStk spatialCouplingReg S).R (cr r) = [])
    (hleft : ∀ k ∈ [(97 : Fin 117),98,99,100], (embStk spatialCouplingReg S).L k = []) (h96 : (embStk spatialCouplingReg S).R 96 = [])
    (hxs : ∀ x ∈ couplingInputWords boundary t band a b i C, Fits w x)
    (has : ∀ z ∈ couplingCoefficientWords P q s t u band i, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ spatialCouplingRowStepCost P q w s t u band i ∧
      Exec body (spatialCouplingRowStep hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update
          (Function.update S.R 113
            (csyms A w (couplingRowWord P q t u band a b i boundary C rhs)++S.R 113))
          93 rhsTail)
          141 (cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
            if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
            then C j else 0) band).drop (i+1))++tail))
          142 ((csyms A w (if ((i : ZMod s)-(band : ZMod s)) ∈
            (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
            then C ((i : ZMod s)-(band : ZMod s)) else 0)).reverse++S.R 142))
          107 (tick::S.R 107))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := outerSpatialCouplingRow_exec (body := body)
    hQ boundary hA hw5 hqw hst hi hP C tail v S
    hPsrc hqsrc husrc hsSrc htSrc hbandSrc hiSrc h105 hwsrc h115 h104 h109 h106 h108
    hblank hsrc h116 h102 rhs rhsTail hrhs hc hcr hleft h96 hxs has
  let z := couplingRowWord P q t u band a b i boundary C rhs
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 113 (csyms A w z++S.R 113)}
  have he₁' : Exec body (outerSpatialCouplingRow hQ) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [S₁,z,couplingRowWord] using he₁
  have hw : (S.R 94).length = w := hwsrc
  have hf104 : S.R 104 = [] := h104
  have hf105 : S.R 105 = [] := h105
  have hrhs' : S.R 93 = csyms A w rhs++rhsTail := hrhs
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := 94) (src := 93) (trash := 104) (tmp := 105) (by decide)
    (csyms A w rhs) rhsTail v₁ S₁ (by simpa [S₁] using hrhs')
    (by simp [S₁,hw]) (by simpa [S₁] using hf104) (by simpa [S₁] using hf105)
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 93 rhsTail}
  let F := fun j : ZMod s => if j ∈
    (if boundary then haloBoundary s t band a b else haloInterior s t band a b) then C j else 0
  have hsource : S.R 141 = cstream A w ((cyclicPaddedLine F band).drop i)++tail := hsrc
  obtain ⟨v₃,hu₃,he₃⟩ := advanceSpatialCouplingCursor_exec (body := body) F band i w hi tail v₂ S₂
    (by simpa [S₂,S₁] using hw) (by simpa [S₂,S₁] using hf105)
    (by simpa [S₂,S₁] using hsource)
  let S₃ : Stacks 144 A := {S₂ with R := (Function.update (Function.update S₂.R
    141 (cstream A w ((cyclicPaddedLine F band).drop (i+1))++tail))
    142 ((csyms A w (F ((i : ZMod s)-(band : ZMod s)))).reverse++S₂.R 142))}
  have he₄ : Exec body (.act (.push (.rt 107) (fun _ => tick) .done)) (mk v₃ S₃) 1
      (mk v₃ {S₃ with R := Function.update S₃.R 107 (tick::S₃.R 107)}) := by
    simpa [Action.run,update_rt] using Exec.act (body := body)
      (.push (.rt 107) (fun _ => tick) .done) (mk v₃ S₃)
  refine ⟨v₃,m₁+((6*w+6)+((4*w+4)+1)),hu₃.trans (hu₂.trans hu₁),
    by dsimp only [spatialCouplingRowStepCost]; omega,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by simp) ?_⟩
  apply congrArg (mk v₃)
  simp only [S₃,S₂,S₁,z,F]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
