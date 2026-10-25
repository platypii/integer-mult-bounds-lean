module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTrimAdvanceLoop

/-! The three final reversals restore the borrowed controls and count and
publish the newly constructed controls. This frame proof is independent of
the parser and its scratch registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

theorem publicationControls_restore {T A : ℕ} {count savedCount control savedControl acc dst : Fin T}
    (hreg : [count,savedCount,control,savedControl,acc,dst].Nodup)
    (R : Regs T A) (cs ct tail ys : List (Fin (A+4)))
    (hc : R count = cs) (hs : R control = ct++tail)
    (hzc : R savedCount = []) (hzs : R savedControl = []) (hza : R acc = []) :
    let R₁ := trimAdvanceUpdate R count savedCount control savedControl acc [] cs.reverse tail ct.reverse ys.reverse
    let R₂ := movedR R₁ acc dst id (R₁ acc)
    let R₃ := movedR R₂ savedControl control id (R₂ savedControl)
    movedR R₃ savedCount count id (R₃ savedCount) = Function.update R dst (ys++R dst) := by
  have hr := hreg
  regs_ne hr
  dsimp only
  funext k
  by_cases hkd : k = dst
  · subst k
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [movedR,trimAdvanceUpdate,hzc,hzs,hza]
  by_cases hkc : k = count
  · subst k
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [movedR,trimAdvanceUpdate,hzc,hzs,hza,hc]
  by_cases hkz : k = savedCount
  · subst k
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [movedR,trimAdvanceUpdate,hzc]
  by_cases hks : k = control
  · subst k
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [movedR,trimAdvanceUpdate,hzc,hzs,hza,hs]
  by_cases hkss : k = savedControl
  · subst k
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [movedR,trimAdvanceUpdate,hzs]
  by_cases hka : k = acc
  · subst k
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [movedR,trimAdvanceUpdate,hza]
  simp [movedR,trimAdvanceUpdate,hkd,hkc,hkz,hks,hkss,hka]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
