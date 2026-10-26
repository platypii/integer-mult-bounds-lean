module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate the fold's half-count, parity and first-half byte count from its retained dimensions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def boundaryFoldCounters : Pr P₀ 117 Q A U :=
  .seq (udiv 2 116 0 4) (.seq (ucopy 116 1 4) (.seq (usub 0 1 4)
    (.seq (ucopy 1 2 4) (.seq (usub 0 2 4)
      (.seq (unaryProduct 1 115 3 4 5) (uclear 1))))))

def boundaryFoldCountersCost (n w : ℕ) : ℕ := n*(4*w+23)+26

theorem boundaryFoldCounters_exec (n w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hn : (S.R 116).length = n) (hw : (S.R 115).length = w)
    (hblank : ∀ r : Fin 117, r.val < 6 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ boundaryFoldCountersCost n w ∧
      Exec body boundaryFoldCounters (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          0 (List.replicate (n/2) tick)) 2 (List.replicate ((n+1)/2-n/2) tick))
          3 (List.replicate (((n+1)/2)*w) tick))}) := by
  have h0 := hblank 0 (by decide)
  have h1 := hblank 1 (by decide)
  have h2 := hblank 2 (by decide)
  have h3 := hblank 3 (by decide)
  have h4 := hblank 4 (by decide)
  have h5 := hblank 5 (by decide)
  let lo := n/2
  let hi := (n+1)/2
  have hsplit : n-lo = hi := by dsimp [lo,hi]; omega
  have hsum : lo+hi = n := by dsimp [lo,hi]; omega
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := udiv_exec (body := body) (c := 2) (by decide)
    (a := 116) (b := 0) (t := 4) (by decide) (by decide) (by decide) v S h4
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 0 (List.replicate lo tick)}
  have he₁' : Exec body (udiv 2 116 0 4) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,lo,hn,h0] using he₁
  have hm₁' : m₁ ≤ 4*n+4 := by simpa only [hn] using hm₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := 116) (b := 1) (t := 4)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using h4)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 1 (List.replicate n tick)}
  have he₂' : Exec body (ucopy 116 1 4) (mk v₁ S₁) (4*n+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hn,h1] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := usub_exec (body := body) (a := 0) (b := 1) (t := 4)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂,S₁] using h4)
  let S₃ : Stacks 117 A := {S₂ with R := Function.update S₂.R 1 (List.replicate hi tick)}
  have he₃' : Exec body (usub 0 1 4) (mk v₂ S₂) (4*lo+4) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,hsplit] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := ucopy_exec (body := body) (a := 1) (b := 2) (t := 4)
    (by decide) (by decide) (by decide) v₃ S₃ (by simpa [S₃,S₂,S₁] using h4)
  let S₄ : Stacks 117 A := {S₃ with R := Function.update S₃.R 2 (List.replicate hi tick)}
  have he₄' : Exec body (ucopy 1 2 4) (mk v₃ S₃) (4*hi+4) (mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,S₁,h2] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := usub_exec (body := body) (a := 0) (b := 2) (t := 4)
    (by decide) (by decide) (by decide) v₄ S₄ (by simpa [S₄,S₃,S₂,S₁] using h4)
  let S₅ : Stacks 117 A := {S₄ with R := Function.update S₄.R 2 (List.replicate (hi-lo) tick)}
  have he₅' : Exec body (usub 0 2 4) (mk v₄ S₄) (4*lo+4) (mk v₅ S₅) := by
    simpa [S₅,S₄,S₃,S₂,S₁] using he₅
  obtain ⟨v₆,m₆,hu₆,hm₆,he₆⟩ := unaryProduct_exec (body := body)
    (a := 1) (b := 115) (dst := 3) (t₁ := 4) (t₂ := 5) (by decide) v₅ S₅
    (by simpa [S₅,S₄,S₃,S₂,S₁] using h4) (by simpa [S₅,S₄,S₃,S₂,S₁] using h5)
  let S₆ : Stacks 117 A := {S₅ with R := Function.update S₅.R 3 (List.replicate (hi*w) tick)}
  have he₆' : Exec body (unaryProduct 1 115 3 4 5) (mk v₅ S₅) m₆ (mk v₆ S₆) := by
    simpa [S₆,S₅,S₄,S₃,S₂,S₁,hw,h3] using he₆
  have hm₆' : m₆ ≤ hi*(4*w+9)+4 := by simpa [S₅,S₄,S₃,S₂,S₁,hw] using hm₆
  obtain ⟨v₇,hu₇,he₇⟩ := uclear_exec (body := body) 1 v₆ S₆
  refine ⟨v₇,m₁+((4*n+4)+((4*lo+4)+((4*hi+4)+((4*lo+4)+(m₆+(2*hi+2)))))),
    hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄'
      (Exec.seq he₅' (Exec.seq he₆' he₇)))))).cast (by simp [S₆,S₅,S₄,S₃]) ?_⟩
  · dsimp [boundaryFoldCountersCost]
    have hhi : hi ≤ n := by omega
    have hprod := Nat.mul_le_mul_right w hhi
    nlinarith only [hm₁',hm₆',hsum,hprod]
  · apply congrArg (mk v₇)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk0 : k = 0 <;> by_cases hk1 : k = 1 <;>
      by_cases hk2 : k = 2 <;> by_cases hk3 : k = 3 <;>
      simp [S₆,S₅,S₄,S₃,S₂,S₁,lo,hi,hk0,hk1,hk2,hk3,h1]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
