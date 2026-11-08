module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedLocalFeedCouplingInterval

/-! Recovery coupling uses the first pass's native counters directly. Its exact
input/output writes preserve the readiness invariant for the next replica. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {A : ℕ}

/-- The exact feed endpoint consumes an input prefix and prepends an output
prefix while retaining all scalar counters and arithmetic workspace. -/
theorem RetainedCouplingReady.feed_frame {P q w s t u band a b : ℕ}
    {raw : List (Fin (A+4))} {S : Stacks 168 A}
    (ready : RetainedCouplingReady P q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg S)))
    (rhsTail output : List (Fin (A+4))) :
    RetainedCouplingReady P q w s t u band a b (output++raw)
      (embStk groupReg (embStk intervalPageReg
        {S with R := (Function.update (Function.update S.R 93 rhsTail) 110
          (output++S.R 110))})) := by
  apply ready.of_source_frame (S' := embStk groupReg (embStk intervalPageReg
    {S with R := (Function.update (Function.update S.R 93 rhsTail) 110
      (output++S.R 110))}))
  · simpa [embStk,groupReg,intervalPageReg] using congrArg (fun xs => output++xs) ready.source
  · rfl
  · intro k h93 _ _ h110
    have hn93 : intervalPageReg (groupReg k) ≠ (93 : Fin 168) := by
      intro h
      apply h93
      apply Fin.ext
      have hv := congrArg (fun i : Fin 168 => i.val) h
      change k.val = 93 at hv ⊢
      exact hv
    have hn110 : intervalPageReg (groupReg k) ≠ (110 : Fin 168) := by
      intro h
      apply h110
      apply Fin.ext
      have hv := congrArg (fun i : Fin 168 => i.val) h
      change k.val = 110 at hv ⊢
      exact hv
    change Function.update (Function.update S.R 93 rhsTail) 110
      (output++S.R 110) (intervalPageReg (groupReg k)) = _
    rw [Function.update_of_ne hn110, Function.update_of_ne hn93]
    rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
