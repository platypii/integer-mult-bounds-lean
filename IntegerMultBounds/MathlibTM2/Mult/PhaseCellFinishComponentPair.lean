module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponentsData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix

/-! Pair the saved real result with the current imaginary result and release the saved page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 148 Q A U}

def finishComponentPair : Pr P₀ 148 Q A U :=
  .seq (ucopy 131 146 134) (.seq (pairComponentsToFirst 146 145 132 147) (movePrefix 131 145 132 147 134))

theorem finishComponentPair_exec (hA : 4 ≤ A) (s w : ℕ) (xs ys : List GaussianInt)
    (hxlen : xs.length = s) (hylen : ys.length = s) (savedTail outputTail : List (Fin (A+4)))
    (v : HS 148 Q A U) (S : Stacks 148 A) (hcount : (S.R 131).length = s*w)
    (hx : S.R 145 = cstream A w xs++savedTail) (hy : S.R 132 = cstream A w ys++outputTail)
    (h134 : S.R 134 = []) (h146 : S.R 146 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 16*s*w+14 ∧
      Exec body finishComponentPair (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 145 savedTail)
          132 (cstream A w (List.zipWith pairComponentWord xs ys)++outputTail))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 131) (b := 146) (t := 134)
    (by decide) (by decide) (by decide) v S h134
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 146 (List.replicate (s*w) tick)}
  have he₁' : Exec body (ucopy 131 146 134) (mk v S) (4*(s*w)+4) (mk v₁ S₁) := by
    simpa [S₁,hcount,h146] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := pairComponentsToFirst_exec (body := body)
    (count := 146) (x := 145) (y := 132) (tmp := 147) (by decide) hA w xs ys (by omega)
    savedTail outputTail v₁ S₁ (by simp [S₁,hxlen])
    (by simpa [S₁] using hx) (by simpa [S₁] using hy) (by simpa [S₁] using h147)
  let Z := cstream A w (List.zipWith pairComponentWord xs ys)
  let S₂ : Stacks 148 A := {S₁ with R := (Function.update (Function.update (Function.update S₁.R
    132 outputTail) 145 (Z++savedTail)) 146 [])}
  obtain ⟨v₃,hu₃,he₃⟩ := movePrefix_exec (body := body)
    (count := 131) (src := 145) (dst := 132) (saved := 147) (tmp := 134) (by decide)
    Z savedTail v₂ S₂ (by simp [S₂]) (by simp [S₂,S₁,Z,hcount,hxlen,hylen])
    (by simpa [S₂,S₁] using h147) (by simpa [S₂,S₁] using h134)
  refine ⟨v₃,(4*(s*w)+4)+(n₂+(6*Z.length+6)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · have hZ : Z.length = s*w := by simp [Z,hxlen,hylen]
    rw [hZ,hxlen] at *
    nlinarith only [hn₂]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h132 : k = 132 <;> by_cases h145 : k = 145 <;> by_cases h146' : k = 146 <;>
      simp [S₂,S₁,Z,h132,h145,h146',h146]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
