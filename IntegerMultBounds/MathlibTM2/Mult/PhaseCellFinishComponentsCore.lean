module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishComponentPair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix

/-! Release the second solve's RHS pages and publish the paired complex result. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 148 Q A U}

def finishComponentsCore : Pr P₀ 148 Q A U :=
  .seq (discardPrefix 131 110 136 134) (.seq (discardPrefix 131 110 136 134) finishComponentPair)

theorem finishComponentsCore_exec (hA : 4 ≤ A) (s w : ℕ) (xs ys : List GaussianInt)
    (hxlen : xs.length = s) (hylen : ys.length = s)
    (recovery rhs tail savedTail outputTail : List (Fin (A+4)))
    (hr : recovery.length = s*w) (hb : rhs.length = s*w)
    (v : HS 148 Q A U) (S : Stacks 148 A) (hcount : (S.R 131).length = s*w)
    (hsrc : S.R 110 = recovery++(rhs++tail))
    (hx : S.R 145 = cstream A w xs++savedTail) (hy : S.R 132 = cstream A w ys++outputTail)
    (h134 : S.R 134 = []) (h136 : S.R 136 = []) (h146 : S.R 146 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 28*s*w+26 ∧
      Exec body finishComponentsCore (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 110 tail) 145 savedTail)
          132 (cstream A w (List.zipWith pairComponentWord xs ys)++outputTail))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 110) (trash := 136) (tmp := 134) (by decide)
    recovery (rhs++tail) v S hsrc (by omega) h136 h134
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 110 (rhs++tail)}
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 110) (trash := 136) (tmp := 134) (by decide)
    rhs tail v₁ S₁ (by simp [S₁]) (by simpa [S₁,hb] using hcount)
    (by simpa [S₁] using h136) (by simpa [S₁] using h134)
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 110 tail}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := finishComponentPair_exec (body := body) hA s w xs ys hxlen hylen
    savedTail outputTail v₂ S₂ (by simpa [S₂,S₁] using hcount)
    (by simpa [S₂,S₁] using hx) (by simpa [S₂,S₁] using hy)
    (by simpa [S₂,S₁] using h134) (by simpa [S₂,S₁] using h146) (by simpa [S₂,S₁] using h147)
  refine ⟨v₃,(6*recovery.length+6)+((6*rhs.length+6)+n₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hr,hb]
    nlinarith only [hn₃]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp [S₂,S₁]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
