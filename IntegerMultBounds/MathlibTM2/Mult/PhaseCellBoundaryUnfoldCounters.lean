module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate the fold's half-count, parity and first-half byte count from its retained dimensions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 224 Q A U}

def boundaryUnfoldCounters : Pr P₀ 224 Q A U :=
  .seq (udiv 2 116 189 223) (.seq (ucopy 116 184 223) (.seq (usub 189 184 223)
    (.seq (ucopy 184 191 223) (.seq (usub 189 191 223) (uclear 184)))))

theorem boundaryUnfoldCounters_exec (n : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hn : (S.R 116).length = n)
    (h189 : S.R 189 = []) (h184 : S.R 184 = []) (h191 : S.R 191 = []) (h223 : S.R 223 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 16*n+22 ∧
      Exec body boundaryUnfoldCounters (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R
          189 (List.replicate (n/2) tick)) 191 (List.replicate ((n+1)/2-n/2) tick))}) := by
  let lo := n/2
  let hi := (n+1)/2
  have hsplit : n-lo = hi := by dsimp [lo,hi]; omega
  have hsum : lo+hi = n := by dsimp [lo,hi]; omega
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := udiv_exec (body := body) (c := 2) (by decide)
    (a := 116) (b := 189) (t := 223) (by decide) (by decide) (by decide) v S h223
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 189 (List.replicate lo tick)}
  have he₁' : Exec body (udiv 2 116 189 223) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,lo,hn,h189] using he₁
  have hm₁' : m₁ ≤ 4*n+4 := by simpa only [hn] using hm₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := 116) (b := 184) (t := 223)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using h223)
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 184 (List.replicate n tick)}
  have he₂' : Exec body (ucopy 116 184 223) (mk v₁ S₁) (4*n+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hn,h184] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := usub_exec (body := body) (a := 189) (b := 184) (t := 223)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂,S₁] using h223)
  let S₃ : Stacks 224 A := {S₂ with R := Function.update S₂.R 184 (List.replicate hi tick)}
  have he₃' : Exec body (usub 189 184 223) (mk v₂ S₂) (4*lo+4) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,hsplit] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := ucopy_exec (body := body) (a := 184) (b := 191) (t := 223)
    (by decide) (by decide) (by decide) v₃ S₃ (by simpa [S₃,S₂,S₁] using h223)
  let S₄ : Stacks 224 A := {S₃ with R := Function.update S₃.R 191 (List.replicate hi tick)}
  have he₄' : Exec body (ucopy 184 191 223) (mk v₃ S₃) (4*hi+4) (mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,S₁,h191] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := usub_exec (body := body) (a := 189) (b := 191) (t := 223)
    (by decide) (by decide) (by decide) v₄ S₄ (by simpa [S₄,S₃,S₂,S₁] using h223)
  let S₅ : Stacks 224 A := {S₄ with R := Function.update S₄.R 191 (List.replicate (hi-lo) tick)}
  have he₅' : Exec body (usub 189 191 223) (mk v₄ S₄) (4*lo+4) (mk v₅ S₅) := by
    simpa [S₅,S₄,S₃,S₂,S₁] using he₅
  obtain ⟨v₆,hu₆,he₆⟩ := uclear_exec body 184 v₅ S₅
  have he₆' : Exec body (uclear 184) (mk v₅ S₅) (2*hi+2)
      (mk v₆ {S₅ with R := Function.update S₅.R 184 []}) := by
    simpa [S₅,S₄,S₃] using he₆
  refine ⟨v₆,m₁+((4*n+4)+((4*lo+4)+((4*hi+4)+((4*lo+4)+(2*hi+2))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅' he₆'))))).cast rfl ?_⟩
  · nlinarith only [hm₁',hsum]
  · apply congrArg (mk v₆)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk189 : k = 189 <;> by_cases hk184 : k = 184 <;> by_cases hk191 : k = 191 <;>
      simp [S₅,S₄,S₃,S₂,S₁,lo,hi,hk189,hk184,hk191,h184]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
