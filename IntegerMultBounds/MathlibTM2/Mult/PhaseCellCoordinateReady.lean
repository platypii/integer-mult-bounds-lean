module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyReady

/-! The selected coordinate is a spectator of the reusable solver invariant. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

theorem LengthKeyReady.update_coordinate {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S : Stacks 144 A}
    (h : LengthKeyReady P N q l s t u band V w input S) (coordinate : List (Fin (A+4))) :
    LengthKeyReady P N q l s t u band V w input
      {S with R := Function.update S.R 139 coordinate} := by
  constructor
  · intro r hr
    have hr139 : r.1 ≠ 139 := by
      simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [Function.update_of_ne hr139] using h.masters r hr
  · exact h.left
  · intro k hk hk93 hk139
    simpa only [Function.update_of_ne (show k ≠ 139 by omega)] using h.blank k hk hk93 hk139
  · simpa using h.source
  · simpa using h.countSaved
  · simpa using h.headerTemp
  · simpa using h.wordWidth
  · simpa using h.keyWidth
  · intro k hk
    have hk139 : k ≠ 139 := by intro he; subst k; norm_num at hk
    simpa only [Function.update_of_ne hk139] using h.fresh k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
