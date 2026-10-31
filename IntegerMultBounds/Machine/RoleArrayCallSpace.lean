module

public import IntegerMultBounds.Machine.RoleArrayCall

/-! Exact payload allocation at a role-array child-call boundary. -/
@[expose] public section
namespace IntegerMultBounds.Machine.RoleArrayCall
open RoleArrayFrames SharedPlacementAlphabet
variable {t a : ℕ}

theorem entered_stack_head (L : Layout t) (ops : List (Role L))
    (src dst : Role L) (n : ℕ) (v : Tapes t a) :
    (entered L ops src dst n v).head L.stack = v.head L.stack+(ops.length*n : ℕ) := by
  simp only [entered,RoleArrayMove.moved,slots,Matrix.cons_val_zero,Matrix.cons_val_one,
    setTape,Function.update_of_ne src.property.1.symm,Function.update_of_ne dst.property.1.symm]
  exact RoleArrayFrames.saved_head L ops n v

end IntegerMultBounds.Machine.RoleArrayCall
