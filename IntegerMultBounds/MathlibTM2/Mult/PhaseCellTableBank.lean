module

public import IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! A small fixed register bank shared by arithmetic packet controllers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def originReg : TblR 16 → Fin 117
  | .v i => ⟨i.val, by omega⟩
  | .wr => 16 | .wn => 17 | .acc => 18
  | .z i => ⟨19+i.val, by omega⟩

theorem originReg_injective : Function.Injective originReg := by
  intro x y h
  cases x <;> cases y <;> simp_all [originReg, Fin.ext_iff]
  all_goals omega

theorem originReg_range (r : TblR 16) : (originReg r).val < 31 := by
  cases r <;> simp [originReg] <;> omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
