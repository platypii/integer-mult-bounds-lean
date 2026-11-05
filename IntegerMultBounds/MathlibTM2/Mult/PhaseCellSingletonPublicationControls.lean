module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationPlan

/-! A singleton publication needs only its origin in symbols, followed by the
restoring sentinel. This exposes the unary controls a physical caller must build. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T A s L : ℕ} {src dst : Fin T}

theorem PreparedPublicationPlan.Ready.singleton
    (plan : PreparedPublicationPlan T src dst) (windows : PublicationWindows s L)
    (a w : ℕ) (horigin : windows.origins = [a])
    (borrowed : List (Fin (A+4))) (S : Stacks T A)
    (hcount : S.R plan.count = [Node.tick])
    (hadvances : S.R plan.advances = gatherControls A [a*w,0]++borrowed)
    (hwindow : (S.R plan.window).length = L*w)
    (hpad : S.R plan.padRows = [])
    (hwidth : (S.R plan.wordWidth).length = w)
    (hfresh : ∀ i ∈ [plan.savedControl,plan.savedAdvances,plan.counter,plan.zero,plan.acc,plan.control,
      plan.trash,plan.tmp,plan.retireCount,plan.gap], S.R i = []) :
    plan.Ready windows w 0 borrowed S := by
  refine ⟨?_,?_,hwindow,?_,hwidth,hfresh⟩
  · simpa [horigin] using hcount
  · simpa [horigin,originAdvances] using hadvances
  · simp [hpad]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
