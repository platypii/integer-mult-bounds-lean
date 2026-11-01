module

public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.Host.Stream

/-! Counted loop plumbing preserves a body's additive stock allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def countedStep (count : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (.pop (.rt count) (fun v _ => v) .done)) (.seq p (.act (peekR count)))

theorem countedStep_exec_within (count : Fin T) (p : Pr P T Q A U)
    (v v' : HS T Q A U) (S F : Stacks T A) (c : Fin (A+4)) (cs : List (Fin (A+4)))
    (hcount : S.R count = c::cs) (hcount' : F.R count = cs) (n depth allowance : ℕ)
    (he : ExecWithin body (fun d z => mnSize z+d ≤
      mnSize (mk v {S with R := Function.update S.R count cs})+depth+allowance) depth p
      (mk v {S with R := Function.update S.R count cs}) n (mk v' F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+allowance) depth
      (countedStep count p) (mk v S) (n+2) (mk {v' with flag := cs.head?.isSome} F) := by
  let M : Stacks T A := {S with R := Function.update S.R count cs}
  have hpop : (.pop (.rt count) (fun v : HS T Q A U => fun _ => v) .done : Act T Q A U).run
      (mk v S) = mk v M := by simp [Action.run,update_rt,hcount,M]
  have hp : Exec body (.act (.pop (.rt count) (fun v _ => v) .done)) (mk v S) 1 (mk v M) :=
    hpop ▸ Exec.act (body := body) (.pop (.rt count) (fun v _ => v) .done) (mk v S)
  have hp' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+0) depth
      (.act (.pop (.rt count) (fun v _ => v) .done)) (mk v S) 1 (mk v M) :=
    mn_native_exec_within hp 0 (by simp [mnNativePushBound,mnActPush]) depth _ (by omega)
  have hq := Exec.act (body := body) (peekR count) (mk v' F)
  rw [peekR_run,hcount'] at hq
  have hq' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v' F)+depth+0) depth
      (.act (peekR count)) (mk v' F) 1 (mk {v' with flag := cs.head?.isSome} F) :=
    mn_native_exec_within hq 0 (by simp [peekR,mnNativePushBound,mnActPush]) depth _ (by omega)
  have hh := mn_seq_within_add hp' (mn_seq_within_add he hq')
  simpa only [countedStep,Nat.zero_add,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

end IntegerMultBounds.MathlibTM2.Host
