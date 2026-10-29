module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryRestoreCouplingCursors
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryRestoreCouplingIndex
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Restore a consumed ribbon prefix using a retained binary local row count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def restoreIntervalCouplingPass : Pr P 168 Q A U :=
  .seq binaryRestoreCouplingCursors (transferCountedLine 139 94 137 138 109 104 105)

theorem restoreIntervalCouplingPass_exec (V N w : ℕ) (hNV : N < 2^V)
    (xs : List GaussianInt) (hlen : N ≤ xs.length) (tail savedTail indexTail : List (Fin (A+4)))
    (coefficients : List GaussianInt) (pageSavedTail : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (h165 : S.R 165 = binSyms V N) (h166 : S.R 166 = []) (hw : (S.R 94).length = w)
    (hsource : S.R 141 = cstream A w (xs.drop N)++tail)
    (hsaved : S.R 142 = (cstream A w (xs.take N)).reverse++savedTail)
    (hindex : S.R 107 = List.replicate N tick++indexTail)
    (h0 : S.R 0 = []) (h1 : S.R 1 = []) (h2 : S.R 2 = [])
    (h139 : (S.R 139).length = coefficients.length)
    (hpageSaved : S.R 137 = (cstream A w coefficients).reverse++pageSavedTail)
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 22*N+22*V+22+transferCountedLineCost N w+transferCountedLineCost coefficients.length w ∧
      Exec body restoreIntervalCouplingPass (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R 107 indexTail)
          142 savedTail) 141 (cstream A w xs++tail)) 137 pageSavedTail)
          138 (cstream A w coefficients++S.R 138))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := binaryRestoreCouplingCursors_exec (body := body) V N w hNV xs hlen
    tail savedTail indexTail v S h165 h166 hw hsource hsaved hindex h0 h1 h2 h109 h104 h105
  let B : Stacks 168 A := {S with R := (Function.update (Function.update (Function.update S.R
    107 indexTail) 142 savedTail) 141 (cstream A w xs++tail))}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := transferCountedLine_exec (body := body)
    139 94 137 138 109 104 105 (by decide) coefficients.length w
    (cstream A w coefficients).reverse pageSavedTail (by simp) v₁ B
    (by simpa [B] using h139) (by simpa [B] using hw) (by simpa [B] using hpageSaved)
    (by simpa [B] using h109) (by simpa [B] using h104) (by simpa [B] using h105)
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  simp [B]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
