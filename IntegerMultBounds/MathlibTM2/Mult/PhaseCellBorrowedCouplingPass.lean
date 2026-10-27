module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageCouplingLines
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCouplingLine

/-! A restoring coupling pass from the original RHS and published solution lines. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def borrowedCouplingPass (hQ : SS.states ≤ Q) (boundary : Bool) : Pr P₀ 144 Q A U :=
  .seq stageCouplingLines (.seq (runCouplingRows hQ boundary) retireCouplingLine)

def borrowedCouplingPassCost (boundary : Bool) (P q w s t u band a b : ℕ) : ℕ :=
  runCouplingRowsCost boundary P q w s t u band a b+38*s*w+18*s+38

theorem borrowedCouplingPass_exec (hQ : SS.states ≤ Q) {P q w s t u band a b : ℕ} [NeZero s]
    (boundary : Bool) (hA : 96 ≤ A) (hw5 : 5 ≤ w) (hqw : q+4 ≤ w)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hP : 13 ≤ P)
    (C B : ZMod s → GaussianInt) (tail sourceTail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b (cstream A w (chirpLine s B)++tail) (embStk groupReg S))
    (hsource : S.R 132 = cstream A w (chirpLine s C)++sourceTail)
    (hindex : S.R 107 = []) (h143 : S.R 143 = [])
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (hxs : ∀ j < s, ∀ x ∈ couplingInputWords boundary t band a b j C, Fits w x)
    (has : ∀ j < s, ∀ z ∈ couplingCoefficientWords P q s t u band j, Fits w z ∧ z.im = 0) :
    ∃ v' m, v'.user = v.user ∧ m ≤ borrowedCouplingPassCost boundary P q w s t u band a b ∧
      Exec (embTab groupReg body) (borrowedCouplingPass hQ boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 113
          (cstream A w (guardedCouplingRowWords P q t u band a b boundary C 0 (chirpLine s B))++S.R 113))}) := by
  have hs : (S.R 97).length = s := hready.axis
  have hwS : (S.R 94).length = w := hready.width
  have hrhs : S.R 110 = cstream A w (chirpLine s B)++tail := hready.source
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := stageCouplingLines_exec (body := embTab groupReg body)
    s w (cstream A w (chirpLine s B)) (cstream A w (chirpLine s C)) tail sourceTail v S hs hwS hrhs hsource
    (by simp) (by simp) h131 h134 h135
  let source := cstream A w (chirpLine s C)
  let rhs := cstream A w (chirpLine s B)
  let S₁ : Stacks 144 A := {S with R := (Function.update (Function.update S.R 93 (rhs++S.R 93))
    110 (source++S.R 110))}
  have hready₁ : CouplingReady P q w s t u band a b
      (source++S.R 110) (embStk groupReg S₁) := by
    apply hready.of_source_frame (S' := embStk groupReg S₁) (raw' := source++S.R 110)
      (by change S₁.R 110 = _; simp [S₁]) rfl
    intro k h93 _ _ h110
    have hn93 : groupReg k ≠ (93 : Fin 144) := by simpa [groupReg,Fin.ext_iff] using h93
    have hn110 : groupReg k ≠ (110 : Fin 144) := by simpa [groupReg,Fin.ext_iff] using h110
    change S₁.R (groupReg k) = S.R (groupReg k)
    simp [S₁,hn93,hn110]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := runCouplingRows_exec (body := body) hQ boundary hA hw5 hqw
    hst haS hbS hbandS hP C (chirpLine s B) (by simp) (S.R 110) (S.R 93) v₁ S₁ hready₁
    (by simpa [S₁] using hindex) (by simp [S₁,rhs]) (by simpa [S₁] using h143)
    (by simpa [S₁] using h135) hxs has
  let ys := guardedCouplingRowWords P q t u band a b boundary C 0 (chirpLine s B)
  let S₂ : Stacks 144 A := {S₁ with R := (Function.update (Function.update S₁.R 93 (S.R 93))
    113 (cstream A w ys++S₁.R 113))}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := retireCouplingLine_exec (body := embTab groupReg body)
    s w source (S.R 110) v₂ S₂ (by simpa [S₂,S₁] using hs) (by simpa [S₂,S₁] using hwS)
    (by simp [S₂,S₁]) (by simp [source]) (by simpa [S₂,S₁] using h131)
    (by simpa [S₂,S₁] using h134) (by simpa [S₂,S₁] using h135)
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · dsimp only [borrowedCouplingPassCost]
    nlinarith only [hm₁,hm₂,hm₃]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h93 : k = 93 <;>
      simp [S₂,S₁,h110,h93,ys,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
