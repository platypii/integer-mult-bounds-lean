module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeLengthKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyReady

/-! Installing generated queue/count/widths establishes the loop invariant
without changing the source, master parameters or private solver workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem initializedKeyRuntimeR_off {A : ℕ} (R : Regs 144 A) (V w K : ℕ)
    (keys : List (Fin (A+4))) (k : Fin 144)
    (h125 : k ≠ 125) (h126 : k ≠ 126) (h127 : k ≠ 127) (h130 : k ≠ 130) :
    initializedKeyRuntimeR R V w K keys k = R k := by
  simp [initializedKeyRuntimeR,h125,h126,h127,h130]

theorem LengthKeyReady.initialized {A P N q l s t u band V₀ w₀ V w K : ℕ}
    {input keys : List (Fin (A+4))} {S : Stacks 144 A}
    (h : LengthKeyReady P N q l s t u band V₀ w₀ input S) :
    LengthKeyReady P N q l s t u band V w input
      { S with R := initializedKeyRuntimeR S.R V w K keys } := by
  constructor
  · intro r hr
    have hoff : r.1 ≠ 125 ∧ r.1 ≠ 126 ∧ r.1 ≠ 127 ∧ r.1 ≠ 130 := by
      simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    change (initializedKeyRuntimeR S.R V w K keys r.1).length = _
    rw [initializedKeyRuntimeR_off _ _ _ _ _ _ hoff.1 hoff.2.1 hoff.2.2.1 hoff.2.2.2]
    exact h.masters r hr
  · exact h.left
  · intro k hk hk93 hk110
    change initializedKeyRuntimeR S.R V w K keys k = []
    rw [initializedKeyRuntimeR_private _ _ _ _ _ _ hk]
    exact h.blank k hk hk93 hk110
  · simpa [initializedKeyRuntimeR] using h.source
  · simpa [initializedKeyRuntimeR] using h.countSaved
  · simpa [initializedKeyRuntimeR] using h.headerTemp
  · simp [initializedKeyRuntimeR]
  · simp [initializedKeyRuntimeR]
  · intro k hk
    have hoff : k ≠ 125 ∧ k ≠ 126 ∧ k ≠ 127 ∧ k ≠ 130 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    change initializedKeyRuntimeR S.R V w K keys k = []
    rw [initializedKeyRuntimeR_off _ _ _ _ _ _ hoff.1 hoff.2.1 hoff.2.2.1 hoff.2.2.2]
    exact h.fresh k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
