module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedDiagonal
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoreRetainedClock

/-! The selected callback followed by restoration of its consumed replica clock.
The frame exposes every unaffected port at once, so packet and workspace
certificates transport without repeating their numerical proofs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def readySelectedDiagonal (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P tapes Q A U :=
  .seq (selectedDiagonal hR hQ) restoreRetainedClock

theorem readySelectedDiagonal_exec
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (v va : HS tapes Q A U) (S advanced : Stacks tapes A)
    (steps stock depth N : ℕ)
    (he : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+stock)
      depth (selectedDiagonal hR hQ) (mk v S) steps (mk va advanced))
    (hready : ClockRestoreInput N advanced) :
    ∃ vr ready, vr.user = va.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(stock+2*(4*N+4)))
        depth (readySelectedDiagonal hR hQ) (mk v S) (steps+(4*N+4)) (mk vr ready) ∧
      ready.R (selector (LocalRecoveryLayout.batch 0)) = List.replicate N tick ∧
      ready.L = advanced.L ∧
      (∀ r, r ≠ selector (LocalRecoveryLayout.batch 0) → ready.R r = advanced.R r) := by
  obtain ⟨vr,hu,hr⟩ := restoreRetainedClock_exec (body := body) N va advanced
    hready.master hready.clock hready.tmp depth
  refine ⟨vr,_,hu,mn_seq_within_add he hr,?_,rfl,?_⟩
  · exact Function.update_self _ _ _
  · intro r hoff
    exact Function.update_of_ne hoff _ _

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
