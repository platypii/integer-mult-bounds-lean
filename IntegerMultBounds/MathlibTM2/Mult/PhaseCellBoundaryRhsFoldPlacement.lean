module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFoldPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRhsSelection

/-! Place the existing fold on RHS records while borrowing the coordinate page and its width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryRhsFoldPlacement

open IntegerMultBounds.MathlibTM2.Fast

def reg (r : RsbR) : Fin 148 :=
  Equiv.swap 109 143 (Equiv.swap 115 94 (BoundaryFoldPlacement.reg r))

theorem reg_injective : Function.Injective reg :=
  (Equiv.injective _).comp ((Equiv.injective _).comp BoundaryFoldPlacement.reg_injective)

@[simp] theorem reg_m2wn : reg .m2wn = 0 := by norm_num [reg,Equiv.swap_apply_def]
@[simp] theorem reg_kn : reg .kn = 2 := by norm_num [reg,Equiv.swap_apply_def]
@[simp] theorem reg_tswn : reg .tswn = 3 := by norm_num [reg,Equiv.swap_apply_def]
@[simp] theorem reg_vk : reg .vk = 6 := by norm_num [reg,Equiv.swap_apply_def]
@[simp] theorem reg_ya : reg .ya = 7 := by norm_num [reg,Equiv.swap_apply_def]
@[simp] theorem reg_xs : reg .xs = 8 := by norm_num [reg,Equiv.swap_apply_def]
@[simp] theorem reg_nv : reg .nv = 9 := by norm_num [reg,Equiv.swap_apply_def]
@[simp] theorem reg_tK : reg .tK = 10 := by norm_num [reg,Equiv.swap_apply_def]
@[simp] theorem reg_tC : reg .tC = 11 := by norm_num [reg,Equiv.swap_apply_def]
@[simp] theorem reg_ac2 : reg .ac2 = 12 := by norm_num [reg,Equiv.swap_apply_def]
@[simp] theorem reg_sel : reg .sel = 143 := by norm_num [reg,Equiv.swap_apply_def]
@[simp] theorem reg_sn : reg .sn = 116 := by norm_num [reg,Equiv.swap_apply_def]
@[simp] theorem reg_width : reg (.cm .wn) = 94 := by norm_num [reg,Equiv.swap_apply_def]

theorem reg_mul (r : RsbR) (i : Fin 64) : reg r ≠ BoundaryFoldPlacement.mul i := by
  have hw : ∀ r i, Equiv.swap 115 94 (BoundaryFoldPlacement.reg r) ≠ BoundaryFoldPlacement.mul i := by
    intro r i
    simpa only [BoundaryFoldPlacement.reg_width] using
      BoundaryFoldPlacement.swap_off BoundaryFoldPlacement.reg_mul (.cm .wn) 94 (by right; decide) r i
  have hs : Equiv.swap 115 94 (BoundaryFoldPlacement.reg .sel) = (109 : Fin 148) := by norm_num [Equiv.swap_apply_def]
  simpa only [hs,reg] using BoundaryFoldPlacement.swap_off hw .sel 143 (by right; decide) r i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryRhsFoldPlacement
