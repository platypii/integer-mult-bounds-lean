module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizationLayout

/-! Eight borrowed recovery ports and one reusable normalization workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedRecoveryNormalization
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def scalar : TblR 25 → Fin 64
  | .v i => ⟨8+i.val,by omega⟩
  | .wr => 33
  | .wn => 34
  | .acc => 35
  | .z i => ⟨36+i.val,by omega⟩

theorem scalar_range (r : TblR 25) : 8 ≤ (scalar r).val ∧ (scalar r).val < 48 := by
  cases r <;> simp [scalar] <;> omega

theorem scalar_injective : Function.Injective scalar := by
  intro r t he
  have hv := congrArg Fin.val he
  cases r <;> cases t <;> simp only [scalar] at hv
  all_goals first | congr 1; exact Fin.ext (by omega) | omega | rfl

def ports (i : Fin 4) : Fin 64 := ⟨48+i.val,by omega⟩

theorem ports_injective : Function.Injective ports := by
  intro i j he
  exact Fin.ext (by have h := congrArg Fin.val he; simp only [ports] at h; omega)

theorem scalar_ne (r : TblR 25) (i : Fin 64) (hi : i.val < 8 ∨ 48 ≤ i.val) : scalar r ≠ i := by
  intro he
  have hr := scalar_range r
  have hv := congrArg Fin.val he
  rcases hi with hi | hi <;> omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedRecoveryNormalization
