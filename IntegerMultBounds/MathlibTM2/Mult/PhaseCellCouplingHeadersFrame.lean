module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCouplingHeaders

/-! Payload changes commute with the private coupling-header overlay. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem couplingHeadersR_update {A : ℕ} (P q s t u band a b : ℕ) (R : Regs 144 A)
    (k : Fin 144) (xs : List (Fin (A+4))) (hk : k ∉ couplingHeaderRegisters) :
    couplingHeadersR P q s t u band a b (Function.update R k xs) =
      Function.update (couplingHeadersR P q s t u band a b R) k xs := by
  have hd : ∀ r ∈ couplingHeaderCopies, r.2 ≠ k := by
    intro r hr he
    apply hk
    rw [← he]
    simp only [couplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [couplingHeaderRegisters]
  funext j
  by_cases hjk : j = k
  · subst j
    rw [couplingHeadersR_off P q s t u band a b _ k hk]
    simp
  · rw [Function.update_of_ne hjk]
    by_cases hj94 : j = 94
    · subst j
      simp [couplingHeadersR]
    · simp only [couplingHeadersR,Function.update_of_ne hj94]
      exact unaryCopiesR_congr_base _ _ _ _ j
        (fun r hr => Function.update_of_ne (hd r hr) xs R) (Function.update_of_ne hjk xs R)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
