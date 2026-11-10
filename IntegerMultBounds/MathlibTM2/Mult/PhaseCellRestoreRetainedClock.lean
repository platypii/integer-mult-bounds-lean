module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicLayout
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Restore the consumed selector clock from its retained replica master.
Only the clock changes; all other banks and the shared buffer are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

structure ClockRestoreInput (N : ℕ) (S : Stacks tapes A) : Prop where
  master : (S.R (aux 7)).length = N
  clock : S.R (selector (LocalRecoveryLayout.batch 0)) = []
  tmp : S.R caller.tmp = []

def restoreRetainedClock : Pr P tapes Q A U :=
  copyR (aux 7) (selector (LocalRecoveryLayout.batch 0)) caller.tmp (fun _ => tick)

private theorem restoreRetainedClock_native :
    mnNativePushBound 2 (restoreRetainedClock (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [restoreRetainedClock,copyR,copyStep,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem restoreRetainedClock_exec (N : ℕ) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hN : (S.R (aux 7)).length = N) (hclock : S.R (selector (LocalRecoveryLayout.batch 0)) = [])
    (htmp : S.R caller.tmp = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(4*N+4)) depth
        restoreRetainedClock (mk v S) (4*N+4)
        (mk v' {S with R := Function.update S.R (selector (LocalRecoveryLayout.batch 0)) (List.replicate N tick)}) := by
  obtain ⟨v',hu,he⟩ := copyR_exec (body := body) (aux 7) (selector (LocalRecoveryLayout.batch 0)) caller.tmp
    (selector_ne_aux _ _).symm (by simp [caller,aux,port_injective.eq_iff]) (selector_ne_aux _ _)
    (fun _ => tick) v S htmp
  have he' : Exec body restoreRetainedClock (mk v S) (4*N+4)
      (mk v' {S with R := Function.update S.R (selector (LocalRecoveryLayout.batch 0)) (List.replicate N tick)}) := by
    simpa only [restoreRetainedClock,List.map_const',hN,List.reverse_replicate,hclock,List.append_nil] using he
  exact ⟨v',hu,mn_native_exec_within he' 2 restoreRetainedClock_native depth _ (by omega)⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
