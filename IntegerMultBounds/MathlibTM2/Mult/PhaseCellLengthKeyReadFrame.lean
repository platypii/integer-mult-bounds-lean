module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyReady

/-! Transfer arithmetic readiness using only the registers that its contract reads. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host

theorem LengthKeyReady.of_read_frame {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S S' : Stacks 144 A}
    (h : LengthKeyReady P N q l s t u band V w input S)
    (hL : S'.L = S.L) (hR : ∀ k : Fin 144, k.val < 141 → S'.R k = S.R k) :
    LengthKeyReady P N q l s t u band V w input S' := by
  constructor
  · intro r hr
    have hbound : r.1.val < 141 := by
      simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hR r.1 hbound]
    exact h.masters r hr
  · intro k hk
    rw [hL]
    exact h.left k hk
  · intro k hk h93 h110
    rw [hR k (by omega)]
    exact h.blank k hk h93 h110
  · rw [hR 110 (by decide)]
    exact h.source
  · rw [hR 129 (by decide)]
    exact h.countSaved
  · rw [hR 133 (by decide)]
    exact h.headerTemp
  · rw [hR 130 (by decide)]
    exact h.wordWidth
  · rw [hR 125 (by decide)]
    exact h.keyWidth
  · intro k hk
    have hbound : k.val < 141 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hR k hbound]
    exact h.fresh k hk

/-- The output accumulator is not read by the arithmetic readiness invariant. -/
theorem LengthKeyReady.of_read_frame_except_output {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S S' : Stacks 144 A}
    (h : LengthKeyReady P N q l s t u band V w input S)
    (hL : S'.L = S.L)
    (hR : ∀ k : Fin 144, k.val < 141 → k ≠ 132 → S'.R k = S.R k) :
    LengthKeyReady P N q l s t u band V w input S' := by
  apply (h.update_output (S'.R 132)).of_read_frame hL
  intro k hk
  by_cases h132 : k = 132
  · subst k; simp
  · simpa only [Function.update_of_ne h132] using hR k hk h132

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
