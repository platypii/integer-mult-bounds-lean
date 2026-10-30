module

public import IntegerMultBounds.MathlibTM2.Fast.TableView

/-! The normalization view of the ordinary inverse scalar bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def inverseRoundVariables : Fin 8 → Fin 25 := ![20,18,0,14,8,15,16,17]

theorem inverseRoundVariables_injective : Function.Injective inverseRoundVariables := by
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all [inverseRoundVariables]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
