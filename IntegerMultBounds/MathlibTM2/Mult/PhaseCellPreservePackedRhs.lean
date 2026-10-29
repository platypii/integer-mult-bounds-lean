module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyCountedLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Preserve the local RHS for residual coupling before the cell solve. The
source and all generated dimension/count scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def preservePackedRhsFrom (precision : Fin 168) : Pr P 168 Q A U :=
  .seq (generateWordWidth precision 94 104)
    (.seq (toUnary 165 166 0 1 2)
      (.seq (copyCountedLine 166 94 110 93 108 104 105) (clearWords [94,166])))

theorem preservePackedRhsFrom_exec (precision : Fin 168) (hreg : [precision,94,104].Nodup)
    (V N q w : ℕ) (hNV : N < 2^V) (hw : w = 2*q+8)
    (E tail : List (Fin (A+4))) (hE : E.length = N*w)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hq : (S.R precision).length = q) (hN : S.R 165 = binSyms V N) (hsource : S.R 110 = E++tail)
    (hclean : ∀ k ∈ [(0 : Fin 168),1,2,94,104,105,108,166], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 16*N*w+17*N+11*V+8*q+2*w+36 ∧
      Exec body (preservePackedRhsFrom precision) (mk v S) m
        (mk v' {S with R := Function.update S.R 93 (E++S.R 93)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body)
    (precision := precision) (width := 94) (tmp := 104) hreg q v S hq
    (hclean 94 (by simp)) (hclean 104 (by simp))
  let B : Stacks 168 A := {S with R := Function.update S.R 94 (List.replicate w tick)}
  have he₁' : Exec body (generateWordWidth precision 94 104) (mk v S) (8*q+9) (mk v₁ B) := by
    simpa only [← hw] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 166) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v₁ B
    (by simpa [B] using hN) (by simpa [B] using hclean 0 (by simp))
    (by simpa [B] using hclean 1 (by simp)) (by simpa [B] using hclean 2 (by simp))
  let C : Stacks 168 A := {B with R := Function.update B.R 166 (List.replicate N tick)}
  have he₂' : Exec body (toUnary 165 166 0 1 2) (mk v₁ B) m₂ (mk v₂ C) := by
    simpa [C,B,hclean 166 (by simp)] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := copyCountedLine_exec (body := body)
    166 94 110 93 108 104 105 (by decide) N w E tail hE v₂ C
    (by simp [C]) (by simp [C,B]) (by simpa [C,B] using hsource)
    (by simpa [C,B] using hclean 108 (by simp))
    (by simpa [C,B] using hclean 104 (by simp))
    (by simpa [C,B] using hclean 105 (by simp))
  let F : Stacks 168 A := {C with R := Function.update C.R 93 (E++C.R 93)}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [(94 : Fin 168),166] (by decide) v₃ F
  have hsum : ([(94 : Fin 168),166].map (fun k => (F.R k).length)).sum = w+N := by simp [F,C,B]
  refine ⟨v₄,(8*q+9)+(m₂+(m₃+(2*(w+N)+5))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by rw [hsum]; simp) ?_⟩
  · dsimp only [copyCountedLineCost] at hm₃
    nlinarith only [hm₂,hm₃]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h94 : k = 94 <;> by_cases h166 : k = 166 <;> by_cases h93 : k = 93 <;>
      simp [F,C,B,h94,h166,h93,hclean 94 (by simp),hclean 166 (by simp)]

/-- The native precision header is the original specialization. -/
def preservePackedRhs : Pr P 168 Q A U := preservePackedRhsFrom 112

theorem preservePackedRhs_exec (V N q w : ℕ) (hNV : N < 2^V) (hw : w = 2*q+8)
    (E tail : List (Fin (A+4))) (hE : E.length = N*w)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hq : (S.R 112).length = q) (hN : S.R 165 = binSyms V N) (hsource : S.R 110 = E++tail)
    (hclean : ∀ k ∈ [(0 : Fin 168),1,2,94,104,105,108,166], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 16*N*w+17*N+11*V+8*q+2*w+36 ∧
      Exec body preservePackedRhs (mk v S) m
        (mk v' {S with R := Function.update S.R 93 (E++S.R 93)}) :=
  preservePackedRhsFrom_exec 112 (by decide) V N q w hNV hw E tail hE v S hq hN hsource hclean

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
