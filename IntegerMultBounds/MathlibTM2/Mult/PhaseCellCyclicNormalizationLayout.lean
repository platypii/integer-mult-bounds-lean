module

public import IntegerMultBounds.MathlibTM2.Fast.TableView

/-! A disjoint rounding bank above the 224-register cyclic solver. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def cyclicSolverReg (i : Fin 224) : Fin 280 := ⟨i.val,by omega⟩

theorem cyclicSolverReg_injective : Function.Injective cyclicSolverReg := by
  intro i j h
  exact Fin.ext (congrArg (Fin.val : Fin 280 → ℕ) h)

def cyclicRoundReg : TblR 25 → Fin 280
  | .v i => ⟨224+i.val,by omega⟩
  | .wr => 249
  | .wn => 250
  | .acc => 251
  | .z i => ⟨252+i.val,by omega⟩

theorem cyclicRoundReg_injective : Function.Injective cyclicRoundReg := by
  intro r t he
  have hv := congrArg Fin.val he
  cases r <;> cases t <;> simp only [cyclicRoundReg] at hv
  all_goals first | congr 1; exact Fin.ext (by omega) | omega | rfl

theorem cyclicRoundReg_range (r : TblR 25) :
    224 ≤ (cyclicRoundReg r).val ∧ (cyclicRoundReg r).val < 264 := by
  cases r <;> simp [cyclicRoundReg] <;> omega

theorem cyclicRoundReg_ne_solver (r : TblR 25) (i : Fin 224) :
    cyclicRoundReg r ≠ cyclicSolverReg i := by
  intro he
  have hv := congrArg Fin.val he
  have hr := (cyclicRoundReg_range r).1
  have hi := i.isLt
  simp only [cyclicSolverReg] at hv
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
