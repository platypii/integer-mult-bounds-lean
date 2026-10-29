module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyCountedLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Retain local publication dimensions and copy the local destination once.
The borrowed source and destination suffixes are preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def preparePackedCellDestination : Pr P 168 Q A U :=
  .seq (generateWordWidth 112 130 104)
    (.seq (ucopy 102 128 104)
      (.seq (toUnary 165 166 0 1 2)
        (.seq (copyCountedLine 166 130 110 132 108 104 105) (uclear 166))))

theorem preparePackedCellDestination_exec (V N L q : ℕ) (hNV : N < 2^V)
    (E tail : List (Fin (A+4))) (hE : E.length = N*(2*q+8))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hq : (S.R 112).length = q) (hL : (S.R 102).length = L)
    (hN : S.R 165 = binSyms V N) (hsource : S.R 110 = E++tail)
    (hclean : ∀ k ∈ [(0 : Fin 168),1,2,104,105,108,128,130,166], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 16*N*(2*q+8)+17*N+11*V+8*q+4*L+37 ∧
      Exec body preparePackedCellDestination (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          130 (List.replicate (2*q+8) tick)) 128 (List.replicate L tick)) 132 (E++S.R 132))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body)
    (precision := 112) (width := 130) (tmp := 104) (by decide) q v S hq
    (hclean 130 (by simp)) (hclean 104 (by simp))
  let W : Stacks 168 A := {S with R := Function.update S.R 130 (List.replicate (2*q+8) tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := 102) (b := 128) (t := 104)
    (by decide) (by decide) (by decide) v₁ W (by simpa [W] using hclean 104 (by simp))
  let D : Stacks 168 A := {W with R := Function.update W.R 128 (List.replicate L tick)}
  have he₂' : Exec body (ucopy 102 128 104) (mk v₁ W) (4*L+4) (mk v₂ D) := by
    simpa [D,W,hL,hclean 128 (by simp)] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 166) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v₂ D
    (by simpa [D,W] using hN) (by simpa [D,W] using hclean 0 (by simp))
    (by simpa [D,W] using hclean 1 (by simp)) (by simpa [D,W] using hclean 2 (by simp))
  let B : Stacks 168 A := {D with R := Function.update D.R 166 (List.replicate N tick)}
  have he₃' : Exec body (toUnary 165 166 0 1 2) (mk v₂ D) m₃ (mk v₃ B) := by
    simpa [B,D,W,hclean 166 (by simp)] using he₃
  obtain ⟨v₄,m₄,hu₄,hm₄,he₄⟩ := copyCountedLine_exec (body := body)
    166 130 110 132 108 104 105 (by decide) N (2*q+8) E tail hE v₃ B
    (by simp [B]) (by simp [B,D,W]) (by simpa [B,D,W] using hsource)
    (by simpa [B,D,W] using hclean 108 (by simp))
    (by simpa [B,D,W] using hclean 104 (by simp))
    (by simpa [B,D,W] using hclean 105 (by simp))
  let F : Stacks 168 A := {B with R := Function.update B.R 132 (E++B.R 132)}
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec (body := body) 166 v₄ F
  have hlen : (F.R 166).length = N := by simp [F,B]
  refine ⟨v₅,(8*q+9)+((4*L+4)+(m₃+(m₄+(2*N+2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ he₅)))).cast (by rw [hlen]) ?_⟩
  · dsimp only [copyCountedLineCost] at hm₄
    nlinarith only [hm₃,hm₄]
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h166 : k = 166 <;> by_cases h132 : k = 132 <;>
      simp [F,B,D,W,h166,h132,hclean 166 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
