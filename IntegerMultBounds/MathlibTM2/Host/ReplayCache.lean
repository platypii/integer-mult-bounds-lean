module

public import IntegerMultBounds.MathlibTM2.Fast.Input
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Replay a retained stream in natural order, restoring both temporary stacks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def replayCache (src dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (copyR src saved tmp id) (moveR saved dst id)

theorem replayCache_exec_within (src dst saved tmp : Fin T)
    (hreg : [src,dst,saved,tmp].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(6*(S.R src).length+6))
        depth (replayCache src dst saved tmp) (mk v S) (6*(S.R src).length+6)
        (mk v' {S with R := Function.update S.R dst (S.R src++S.R dst)}) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg
  obtain ⟨⟨hsd,hss,hst⟩,⟨⟨hds,hdt⟩,⟨hstmp,_⟩⟩⟩ := hreg
  have hsd' := Ne.symm hds
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec (body := body) src saved tmp
    (by assumption) (by assumption) (by assumption) id v S htmp
  let B : Stacks T A := {S with R := Function.update S.R saved (S.R src).reverse}
  have hcopy : Exec body (copyR src saved tmp id) (mk v S) (4*(S.R src).length+4) (mk v₁ B) := by
    simpa only [List.map_id,hsaved,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (body := body) saved dst (by assumption) id v₁ B
  have htrace : Exec body (replayCache src dst saved tmp) (mk v S) (6*(S.R src).length+6)
      (mk v₂ {S with R := Function.update S.R dst (S.R src++S.R dst)}) := by
    refine (Exec.seq hcopy he₂).cast ?_ ?_
    · simp [B]; omega
    · apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hd : k = dst <;> by_cases hs : k = saved <;>
        simp_all [B,movedR]
  refine ⟨v₂,hu₂.trans hu₁,?_⟩
  intro depth
  apply mn_native_exec_within htrace 2 ?_ depth _ (by omega)
  simp [replayCache,copyR,copyStep,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Host
