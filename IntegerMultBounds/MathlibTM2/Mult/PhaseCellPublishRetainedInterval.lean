module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalDiagonalLayout
public import IntegerMultBounds.MathlibTM2.Host.OrderedMoveStock

/-! Publish one completed batch to a persistent archive and retire its diagonal
output. Borrowed archive suffixes survive; transfer allocates no tape symbols. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def publishDiagonal : Pr P tapes Q A U :=
  moveRightOrdered (selector (LocalRecoveryLayout.diagonalRole .dst)) caller.tmp outputArchive

theorem publishDiagonal_exec (v : HS tapes Q A U) (S : Stacks tapes A)
    (packet : List (Fin (A+4))) (hpacket : S.R (selector (LocalRecoveryLayout.diagonalRole .dst)) = packet)
    (htmp : S.R caller.tmp = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth) depth
        publishDiagonal (mk v S) (4*packet.length+4)
        (mk v' {S with R := (Function.update
          (Function.update S.R (selector (LocalRecoveryLayout.diagonalRole .dst)) [])
          outputArchive (packet++S.R outputArchive))}) := by
  obtain ⟨v',hu,he⟩ := moveRightOrdered_exec (body := body)
    (selector (LocalRecoveryLayout.diagonalRole .dst)) caller.tmp outputArchive
    (selector_ne_aux _ _) (selector_ne_aux _ _)
    (by simp [caller,outputArchive,aux,port_injective.eq_iff]) v S htmp
  have hw := moveRightOrdered_within _ _ _ he depth (mnSize (mk v S)+depth) (by omega)
  refine ⟨v',hu,?_⟩
  simpa only [publishDiagonal,hpacket] using hw

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
