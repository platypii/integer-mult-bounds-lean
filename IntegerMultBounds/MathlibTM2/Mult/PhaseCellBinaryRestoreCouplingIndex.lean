module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Host.BinArith

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def binaryRestoreCouplingIndex : Pr P 168 Q A U :=
  .seq (toUnary 165 166 0 1 2) (.seq (discardPrefix 166 107 104 105) (uclear 166))

theorem binaryRestoreCouplingIndex_exec (V N : ℕ) (hNV : N < 2^V)
    (indexTail : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (hindex : S.R 107 = List.replicate N tick++indexTail)
    (h0 : S.R 0 = []) (h1 : S.R 1 = []) (h2 : S.R 2 = [])
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 14*N+11*V+14 ∧
      Exec body binaryRestoreCouplingIndex (mk v S) n
        (mk v' {S with R := Function.update S.R 107 indexTail}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 166) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v S h165 h0 h1 h2
  let B : Stacks 168 A := {S with R := Function.update S.R 166 (List.replicate N tick)}
  have he₁' : Exec body (toUnary 165 166 0 1 2) (mk v S) n₁ (mk v₁ B) := by
    simpa only [h166,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := 166) (src := 107) (trash := 104) (tmp := 105) (by decide)
    (List.replicate N tick) indexTail v₁ B (by simpa [B] using hindex) (by simp [B])
    (by simpa [B] using h104) (by simpa [B] using h105)
  let F : Stacks 168 A := {B with R := Function.update B.R 107 indexTail}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 166 v₂ F
  have hcount : (F.R 166).length = N := by simp [F,B]
  refine ⟨v₃,n₁+((6*N+6)+(2*N+2)),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by simp only [List.length_replicate]; rw [hcount]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases hi : r = 107 <;> by_cases hc : r = 166 <;> simp [F,B,hi,hc,h166]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
