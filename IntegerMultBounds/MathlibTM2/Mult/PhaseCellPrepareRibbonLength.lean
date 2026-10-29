module

public import IntegerMultBounds.MathlibTM2.Host.BinArith

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def prepareRibbonLength : Pr P 168 Q A U :=
  .seq (umul 2 100 166 109) (toUnary 165 166 0 1 2)

theorem prepareRibbonLength_exec (V N band : ℕ) (hNV : N < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = [])
    (hband : (S.R 100).length = band) (h109 : S.R 109 = [])
    (h0 : S.R 0 = []) (h1 : S.R 1 = []) (h2 : S.R 2 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6*N+4*band+11*V+10 ∧
      Exec body prepareRibbonLength (mk v S) n
        (mk v' {S with R := Function.update S.R 166 (List.replicate (N+2*band) tick)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := umul_exec (body := body) 2 (a := 100) (b := 166) (t := 109)
    (by decide) (by decide) (by decide) v S h109
  let B : Stacks 168 A := {S with R := Function.update S.R 166 (List.replicate (2*band) tick)}
  have he₁' : Exec body (umul 2 100 166 109) (mk v S) (4*band+4) (mk v₁ B) := by
    simpa [B,hband,h166] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 166) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v₁ B
    (by simpa [B] using h165) (by simpa [B] using h0)
    (by simpa [B] using h1) (by simpa [B] using h2)
  refine ⟨v₂,4*band+4+n₂,hu₂.trans hu₁,by omega,(Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  simp only [B,Function.update_self,← List.replicate_add,Function.update_idem]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
