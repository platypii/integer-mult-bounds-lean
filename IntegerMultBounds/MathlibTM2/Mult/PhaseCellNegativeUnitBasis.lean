module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNegativeUnitWord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellZeroWords

/-! Generate an ambient negative basis vector at its retained unary coordinate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def negativeUnitWords (q n j : ℕ) : List GaussianInt :=
  List.replicate j 0++[⟨-(2 : ℤ)^q,0⟩]++List.replicate (n-j-1) 0

def negativeUnitBasis : Pr P₀ 144 Q A U :=
  .seq (ucopy 97 131 135) (.seq (.act (dropTop 131 .done)) (.seq (usub 136 131 135)
    (.seq (zeroWords 131 94 132 134 135 137) (.seq (uclear 131)
      (.seq (negativeUnitWord 94 112 132 131 135) (zeroWords 136 94 132 134 135 137))))))

theorem negativeUnitBasis_exec (n j w q : ℕ) (hj : j < n) (hq : q ≤ w)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hn : (S.R 97).length = n) (hjS : (S.R 136).length = j)
    (hw : (S.R 94).length = w) (hqS : (S.R 112).length = q)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) (h137 : S.R 137 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 10*n*w+17*n+2*q+40 ∧
      Exec body negativeUnitBasis (mk v S) m
        (mk v' {S with R := Function.update S.R 132 (cstream A w (negativeUnitWords q n j)++S.R 132)}) := by
  let r := n-j-1
  have hrest : n-1-j = r := by dsimp [r]; omega
  have hsplit : r+j+1 = n := by dsimp [r]; omega
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 97) (b := 131) (t := 135)
    (by decide) (by decide) (by decide) v S h135
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 131 (List.replicate n tick)}
  have he₁' : Exec body (ucopy 97 131 135) (mk v S) (4*n+4) (mk v₁ S₁) := by
    simpa [S₁,hn,h131] using he₁
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 131 (List.replicate (n-1) tick)}
  have he₂ : Exec body (.act (dropTop 131 .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    simpa [S₂,S₁,dropTop,Action.run,update_rt] using Exec.act (body := body) (dropTop 131 .done) (mk v₁ S₁)
  obtain ⟨v₃,hu₃,he₃⟩ := usub_exec (body := body) (a := 136) (b := 131) (t := 135)
    (by decide) (by decide) (by decide) v₁ S₂ (by simpa [S₂,S₁] using h135)
  let S₃ : Stacks 144 A := {S₂ with R := Function.update S₂.R 131 (List.replicate r tick)}
  have he₃' : Exec body (usub 136 131 135) (mk v₁ S₂) (4*j+4) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,hjS,hrest] using he₃
  obtain ⟨v₄,m₄,hu₄,hm₄,he₄⟩ := zeroWords_exec (body := body)
    (rows := 131) (width := 94) (dst := 132) (count := 134) (saved := 135) (tmp := 137) (by decide)
    r w v₃ S₃ (by simp [S₃]) (by simpa [S₃,S₂,S₁] using hw)
    (by simpa [S₃,S₂,S₁] using h134) (by simpa [S₃,S₂,S₁] using h135) (by simpa [S₃,S₂,S₁] using h137)
  let S₄ : Stacks 144 A := {S₃ with R := Function.update S₃.R 132 (cstream A w (List.replicate r 0)++S.R 132)}
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec (body := body) 131 v₄ S₄
  let S₅ : Stacks 144 A := {S₄ with R := Function.update S₄.R 131 []}
  obtain ⟨v₆,hu₆,he₆⟩ := negativeUnitWord_exec (body := body)
    (width := 94) (precision := 112) (dst := 132) (rest := 131) (saved := 135) (by decide) w q hq v₅ S₅
    (by simpa [S₅,S₄,S₃,S₂,S₁] using hw) (by simpa [S₅,S₄,S₃,S₂,S₁] using hqS)
    (by simp [S₅]) (by simpa [S₅,S₄,S₃,S₂,S₁] using h135)
  let S₆ : Stacks 144 A := {S₅ with R := (Function.update S₅.R 132
    (csyms A w (⟨-(2 : ℤ)^q,0⟩ : GaussianInt)++S₅.R 132))}
  obtain ⟨v₇,m₇,hu₇,hm₇,he₇⟩ := zeroWords_exec (body := body)
    (rows := 136) (width := 94) (dst := 132) (count := 134) (saved := 135) (tmp := 137) (by decide)
    j w v₆ S₆ (by simpa [S₆,S₅,S₄,S₃,S₂,S₁] using hjS) (by simpa [S₆,S₅,S₄,S₃,S₂,S₁] using hw)
    (by simpa [S₆,S₅,S₄,S₃,S₂,S₁] using h134) (by simpa [S₆,S₅,S₄,S₃,S₂,S₁] using h135)
    (by simpa [S₆,S₅,S₄,S₃,S₂,S₁] using h137)
  refine ⟨v₇,(4*n+4)+(1+((4*j+4)+(m₄+((2*r+2)+((10*w+2*q+18)+m₇))))),
    hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans hu₁)))),?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆ he₇)))))).cast
      (by simp [S₄,S₃]) ?_⟩
  · have hprod := congrArg (fun k => k*w) hsplit
    nlinarith only [hm₄,hm₇,hprod,hsplit,hj]
  · apply congrArg (mk v₇)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h132 : k = 132 <;> by_cases h131' : k = 131 <;>
      simp [S₆,S₅,S₄,S₃,S₂,S₁,h132,h131',h131,negativeUnitWords,r,cstream_append,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
