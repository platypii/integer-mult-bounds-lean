module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCropCounters

/-! Boundary arithmetic shares the existing 117-register bank. Its table lives
above all restoring-stage roles and writes the retained skip/core-bit masters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast.TableVM

def boundaryCounterRegister : TblR 9 → Fin 117
  | .v i => ⟨30+i.val,by have := i.isLt; omega⟩
  | .wr => 39
  | .wn => 40
  | .acc => 41
  | .z i => ⟨42+i.val,by have := i.isLt; omega⟩

theorem boundaryCounterRegister_injective : Function.Injective boundaryCounterRegister := by
  intro x y h
  cases x <;> cases y <;> simp only [boundaryCounterRegister,Fin.ext_iff] at h
  all_goals (try have := ‹Fin 9›.isLt) <;> (try have := ‹Fin 12›.isLt)
  all_goals first | rfl | congr 1; apply Fin.ext; omega | omega

theorem boundaryCounterRegister_bounds (r : TblR 9) :
    30 ≤ (boundaryCounterRegister r).val ∧ (boundaryCounterRegister r).val < 54 := by
  cases r <;> simp only [boundaryCounterRegister,Fin.val_ofNat,Fin.val_mk]
  all_goals (try have := ‹Fin _›.isLt) <;> omega

def standardBoundaryCounterProgram {Q A : ℕ} {P U : Type} (last : Bool) : Pr P 117 Q A U :=
  BoundaryCropMetadata.counterProgram boundaryCounterRegister last 26 24

theorem boundaryCounterRegister_off_masters (r : TblR 9) :
    boundaryCounterRegister r ≠ 26 ∧ boundaryCounterRegister r ≠ 24 := by
  have hb := boundaryCounterRegister_bounds r
  constructor <;> intro h <;> have he := congrArg Fin.val h <;> simp at he <;> omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
