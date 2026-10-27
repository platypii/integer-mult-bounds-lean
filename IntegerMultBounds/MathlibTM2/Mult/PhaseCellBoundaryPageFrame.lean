module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryWorkspace

/-! The resident coordinate page is invisible to the relocated arithmetic bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

theorem tableArithmeticProject_page {A : ℕ} (S : Stacks 154 A)
    (page width count : List (Fin (A+4))) :
    embStk boundaryArithmeticReg (embStk tableReg {S with R := (Function.update (Function.update
      (Function.update S.R 115 width) 116 count) 109 page)}) =
      embStk boundaryArithmeticReg (embStk tableReg S) := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  obtain ⟨h109,h115,h116⟩ := boundaryArithmeticReg_off i
  have h109' : tableReg (boundaryArithmeticReg i) ≠ 109 := by
    change tableReg (boundaryArithmeticReg i) ≠ tableReg 109
    exact fun h => h109 (tableReg_injective h)
  have h115' : tableReg (boundaryArithmeticReg i) ≠ 115 := by
    change tableReg (boundaryArithmeticReg i) ≠ tableReg 115
    exact fun h => h115 (tableReg_injective h)
  have h116' : tableReg (boundaryArithmeticReg i) ≠ 116 := by
    change tableReg (boundaryArithmeticReg i) ≠ tableReg 116
    exact fun h => h116 (tableReg_injective h)
  simp [embStk,Function.comp_def,h109',h115',h116']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
