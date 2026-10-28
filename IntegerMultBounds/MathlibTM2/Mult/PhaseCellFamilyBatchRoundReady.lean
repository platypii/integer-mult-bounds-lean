module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseCallerWorkspace

/-! Released batch-caller core ports supply the rounding pass's entire scratch frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

theorem inverseSmallPorts_blank {A : ℕ} (S : Stacks 303 A)
    (hblank : ∀ i : Fin 263, i ≠ 110 → i ≠ 132 → i ≠ 246 → S.R (familyInverseCoreReg i) = []) :
    ∀ r ∈ ([0,1,2,3,4,5,6,7,8] : List (Fin 303)), S.R r = [] := by
  intro r hr
  have hlo : r.val ≤ 8 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  let i : Fin 263 := ⟨r.val,by omega⟩
  have hi (n : Fin 263) (hn : 8 < n.val) : i ≠ n := by
    intro he
    have hv := congrArg (fun k : Fin 263 => k.val) he
    dsimp [i] at hv
    omega
  have hh := hblank i (hi 110 (by decide)) (hi 132 (by decide)) (hi 246 (by decide))
  have he : familyInverseCoreReg i = r := by
    apply Fin.ext
    simp [familyInverseCoreReg,i,show r.val < 224 by omega]
  rwa [he] at hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
