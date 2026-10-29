module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryRestoreCouplingRibbon
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryRestoreCouplingIndex
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Restore a consumed ribbon prefix using a retained binary local row count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def binaryRestoreCouplingCursors : Pr P 168 Q A U :=
  .seq binaryRestoreCouplingIndex binaryRestoreCouplingRibbon

theorem binaryRestoreCouplingCursors_exec (V N w : ℕ) (hNV : N < 2^V)
    (xs : List GaussianInt) (hlen : N ≤ xs.length) (tail savedTail indexTail : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = []) (hw : (S.R 94).length = w)
    (hsource : S.R 141 = cstream A w (xs.drop N)++tail)
    (hsaved : S.R 142 = (cstream A w (xs.take N)).reverse++savedTail)
    (hindex : S.R 107 = List.replicate N tick++indexTail)
    (h0 : S.R 0 = []) (h1 : S.R 1 = []) (h2 : S.R 2 = [])
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 22*N+22*V+22+transferCountedLineCost N w ∧
      Exec body binaryRestoreCouplingCursors (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 107 indexTail)
          142 savedTail) 141 (cstream A w xs++tail))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := binaryRestoreCouplingIndex_exec (body := body) V N hNV indexTail v S
    h165 h166 hindex h0 h1 h2 h104 h105
  let B : Stacks 168 A := {S with R := Function.update S.R 107 indexTail}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := binaryRestoreCouplingRibbon_exec (body := body) V N w hNV xs hlen
    tail savedTail v₁ B (by simpa [B] using h165) (by simpa [B] using h166)
    (by simpa [B] using hw) (by simpa [B] using hsource) (by simpa [B] using hsaved)
    (by simpa [B] using h0) (by simpa [B] using h1) (by simpa [B] using h2)
    (by simpa [B] using h109) (by simpa [B] using h104) (by simpa [B] using h105)
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
