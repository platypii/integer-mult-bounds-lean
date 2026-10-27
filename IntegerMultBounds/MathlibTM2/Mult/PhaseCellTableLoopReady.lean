module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentWorkspace

/-! Transfer solver readiness through arbitrary accumulated table prefixes and outer controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host

theorem LengthKeyReady.of_registers {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S S' : Stacks 144 A}
    (h : LengthKeyReady P N q l s t u band V w input S) (hL : S'.L = S.L) (hR : S'.R = S.R) :
    LengthKeyReady P N q l s t u band V w input S' := by
  constructor
  · simpa only [hR] using h.masters
  · simpa only [hL] using h.left
  · simpa only [hR] using h.blank
  · simpa only [hR] using h.source
  · simpa only [hR] using h.countSaved
  · simpa only [hR] using h.headerTemp
  · simpa only [hR] using h.wordWidth
  · simpa only [hR] using h.keyWidth
  · simpa only [hR] using h.fresh

theorem tableLoopReady_of_frame {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S S' : Stacks 154 A}
    (h : LengthKeyReady P N q l s t u band V w input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S))))
    (hL : S'.L = S.L)
    (hframe : ∀ k : Fin 154, k.val < 151 → k ≠ 132 → S'.R k = S.R k) :
    LengthKeyReady P N q l s t u band V w input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))) := by
  let e := fun i : Fin 144 => tableReg (boundaryArithmeticReg (componentReg i))
  have he : Function.Injective e := tableReg_injective.comp (boundaryArithmeticReg_injective.comp componentReg_injective)
  have hR : (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S'))).R =
      Function.update (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S))).R
        132 (S'.R 132) := by
    funext i
    by_cases hi : i = 132
    · subst i; simp [embStk,componentReg,boundaryArithmeticReg,tableReg]
    rw [Function.update_of_ne hi]
    change S'.R (e i) = S.R (e i)
    apply hframe
    · exact (boundaryArithmeticReg (componentReg i)).isLt
    · change e i ≠ e 132
      exact fun hh => hi (he hh)
  apply (h.update_output (S'.R 132)).of_registers
  · funext i
    change S'.L (e i) = S.L (e i)
    rw [hL]
  · exact hR

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
