module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine

/-! Retire recovery's owned residual prefix using retained row and word-width masters. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPageRetireResidual : Pr P 240 Q A U :=
  retireCountedLine 121 160 110 231 232 233

def sharedPageRetireResidualCost (s w : ℕ) : ℕ := s*(12*w+9)+12

theorem sharedPageRetireResidual_exec (s w : ℕ) (residual tail : List (Fin (A+4)))
    (hlen : residual.length = s*w) (v : HS 240 Q A U) (S : Stacks 240 A)
    (hs : (S.R 121).length = s) (hw : (S.R 160).length = w)
    (hsource : S.R 110 = residual++tail)
    (h231 : S.R 231 = []) (h232 : S.R 232 = []) (h233 : S.R 233 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ sharedPageRetireResidualCost s w ∧
      Exec body sharedPageRetireResidual (mk v S) n
        (mk v' {S with R := Function.update S.R 110 tail}) := by
  exact retireCountedLine_exec 121 160 110 231 232 233 (by decide) s w residual tail hlen v S
    hs hw hsource h231 h232 h233

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
