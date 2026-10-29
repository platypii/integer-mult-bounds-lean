module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTransferCountedLine
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Restore a consumed ribbon prefix using a retained binary local row count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def binaryRestoreCouplingRibbon : Pr P 168 Q A U :=
  .seq (toUnary 165 166 0 1 2)
    (.seq (transferCountedLine 166 94 142 141 109 104 105) (uclear 166))

theorem binaryRestoreCouplingRibbon_exec (V N w : ℕ) (hNV : N < 2^V)
    (xs : List GaussianInt) (hlen : N ≤ xs.length) (tail savedTail : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = []) (hw : (S.R 94).length = w)
    (hsource : S.R 141 = cstream A w (xs.drop N)++tail)
    (hsaved : S.R 142 = (cstream A w (xs.take N)).reverse++savedTail)
    (h0 : S.R 0 = []) (h1 : S.R 1 = []) (h2 : S.R 2 = [])
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 8*N+11*V+8+transferCountedLineCost N w ∧
      Exec body binaryRestoreCouplingRibbon (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R
          142 savedTail) 141 (cstream A w xs++tail))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 166) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v S h165 h0 h1 h2
  let B : Stacks 168 A := {S with R := Function.update S.R 166 (List.replicate N tick)}
  have he₁' : Exec body (toUnary 165 166 0 1 2) (mk v S) n₁ (mk v₁ B) := by
    simpa only [h166,List.append_nil] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := transferCountedLine_exec (body := body)
    166 94 142 141 109 104 105 (by decide) N w (cstream A w (xs.take N)).reverse savedTail
    (by simp [List.length_take,Nat.min_eq_left hlen]) v₁ B (by simp [B])
    (by simpa [B] using hw) (by simpa [B] using hsaved)
    (by simpa [B] using h109) (by simpa [B] using h104) (by simpa [B] using h105)
  let F : Stacks 168 A := {B with R := (Function.update (Function.update B.R
    142 savedTail) 141 (cstream A w xs++tail))}
  have he₂' : Exec body (transferCountedLine 166 94 142 141 109 104 105)
      (mk v₁ B) n₂ (mk v₂ F) := by
    simpa [F,B,hsource,← List.append_assoc,← cstream_append,List.take_append_drop] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 166 v₂ F
  have hcount : (F.R 166).length = N := by simp [F,B]
  refine ⟨v₃,n₁+(n₂+(2*N+2)),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast (by rw [hcount]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases h141 : r = 141 <;> by_cases h142 : r = 142 <;> by_cases hc : r = 166 <;>
    simp [F,B,h141,h142,hc,h166]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
