module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalDiagonalLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBulkSelectionCounts

/-! The retained recovery dimensions generate the diagonal loop's private rulers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

noncomputable def diagonalBatchCounts : Pr P tapes Q A U :=
  bulkSelectionCounts (recovery (.control .replicas)) (recovery (.control .cropRows))
    (recovery (.control .packet)) diagonalClock diagonalBytes diagonalSaved diagonalTmp

theorem diagonalBatchCounts_exec (N rows w : ℕ) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hN : (S.R (recovery (.control .replicas))).length = N)
    (hrows : (S.R (recovery (.control .cropRows))).length = rows)
    (hw : (S.R (recovery (.control .packet))).length = w)
    (hblank : ∀ k ∈ [diagonalClock,diagonalBytes,diagonalSaved,diagonalTmp], S.R k = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ bulkSelectionCountsCost N rows w ∧
      Exec body diagonalBatchCounts (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update (Function.update S.R diagonalClock (List.replicate N tick))
          diagonalBytes (List.replicate (rows*w) tick))}) ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        2*bulkSelectionCountsCost N rows w) depth diagonalBatchCounts (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update (Function.update S.R diagonalClock (List.replicate N tick))
          diagonalBytes (List.replicate (rows*w) tick))}) := by
  exact bulkSelectionCounts_exec (body := body) _ _ _ _ _ _ _
    (by simp [diagonalClock,diagonalBytes,diagonalSaved,diagonalTmp,recovery_injective.eq_iff])
    N rows w v S hN hrows hw hblank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
