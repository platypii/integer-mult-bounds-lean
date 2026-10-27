module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth

/-! Reconstruct the fixed-point word width from retained outer precision. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def couplingHeaderWidth : Pr P₀ 144 Q A U := generateWordWidth 119 94 135

theorem couplingHeaderWidth_exec (q : ℕ) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hq : (S.R 119).length = q) (h94 : S.R 94 = []) (h135 : S.R 135 = []) :
    ∃ v', v'.user = v.user ∧ Exec body couplingHeaderWidth (mk v S) (8*q+9)
      (mk v' {S with R := Function.update S.R 94 (List.replicate (2*q+8) tick)}) := by
  simpa [couplingHeaderWidth] using generateWordWidth_exec (body := body)
    (precision := 119) (width := 94) (tmp := 135) (by decide) q v S hq h94 h135

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
