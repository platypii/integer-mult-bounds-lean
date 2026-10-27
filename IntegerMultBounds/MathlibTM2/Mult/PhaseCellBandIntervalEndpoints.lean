module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate the start and upper endpoint of a folded-band interval from unary headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def bandIntervalEndpoints (index band cursor count tmp : Fin T) : Pr P T Q A U :=
  .seq (ucopy index cursor tmp) (.seq (usub band cursor tmp) (.seq (ucopy index count tmp) (.seq (ucopy band count tmp) (.act (.push (.rt count) (fun _ => tick) .done)))))

def bandIntervalEndpointsCost (n W : ℕ) : ℕ :=
  [4*(n)+4,4*(W)+4,4*(n)+4,4*(W)+4,1].sum

theorem bandIntervalEndpoints_exec {index band cursor count tmp : Fin T}
    (hreg : [index,band,cursor,count,tmp].Nodup) (n W : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hn : (S.R index).length = n) (hW : (S.R band).length = W)
    (hfresh : ∀ k ∈ [cursor,count,tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (bandIntervalEndpoints index band cursor count tmp) (mk v S)
        (bandIntervalEndpointsCost n W)
        (mk v' {S with R := (Function.update (Function.update S.R cursor (List.replicate (n-W) tick))
          count (List.replicate (n+W+1) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v1,hu1,he1⟩ := ucopy_exec body (a := index) (b := cursor) (t := tmp)
    ‹index ≠ cursor› ‹index ≠ tmp› ‹cursor ≠ tmp› v S (by simpa [hn,hW,hfresh cursor (by simp),hfresh count (by simp),hfresh tmp (by simp),‹index ≠ band›,‹index ≠ band›.symm,‹index ≠ cursor›,‹index ≠ cursor›.symm,‹index ≠ count›,‹index ≠ count›.symm,‹index ≠ tmp›,‹index ≠ tmp›.symm,‹band ≠ cursor›,‹band ≠ cursor›.symm,‹band ≠ count›,‹band ≠ count›.symm,‹band ≠ tmp›,‹band ≠ tmp›.symm,‹cursor ≠ count›,‹cursor ≠ count›.symm,‹cursor ≠ tmp›,‹cursor ≠ tmp›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm] using hfresh tmp (by simp))
  let S1 : Stacks T A := {S with R := Function.update S.R cursor (List.replicate (n) tick)}
  have he1' : Exec body (ucopy index cursor tmp) (mk v S) (4*(n)+4) (mk v1 S1) := by
    simpa [S1,hn,hW,hfresh cursor (by simp),hfresh count (by simp),hfresh tmp (by simp),‹index ≠ band›,‹index ≠ band›.symm,‹index ≠ cursor›,‹index ≠ cursor›.symm,‹index ≠ count›,‹index ≠ count›.symm,‹index ≠ tmp›,‹index ≠ tmp›.symm,‹band ≠ cursor›,‹band ≠ cursor›.symm,‹band ≠ count›,‹band ≠ count›.symm,‹band ≠ tmp›,‹band ≠ tmp›.symm,‹cursor ≠ count›,‹cursor ≠ count›.symm,‹cursor ≠ tmp›,‹cursor ≠ tmp›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm,List.drop_replicate,Action.run,update_rt,List.replicate_succ] using he1
  obtain ⟨v2,hu2,he2⟩ := usub_exec body (a := band) (b := cursor) (t := tmp)
    ‹band ≠ cursor› ‹band ≠ tmp› ‹cursor ≠ tmp› v1 S1 (by simpa [S1,hn,hW,hfresh cursor (by simp),hfresh count (by simp),hfresh tmp (by simp),‹index ≠ band›,‹index ≠ band›.symm,‹index ≠ cursor›,‹index ≠ cursor›.symm,‹index ≠ count›,‹index ≠ count›.symm,‹index ≠ tmp›,‹index ≠ tmp›.symm,‹band ≠ cursor›,‹band ≠ cursor›.symm,‹band ≠ count›,‹band ≠ count›.symm,‹band ≠ tmp›,‹band ≠ tmp›.symm,‹cursor ≠ count›,‹cursor ≠ count›.symm,‹cursor ≠ tmp›,‹cursor ≠ tmp›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm] using hfresh tmp (by simp))
  let S2 : Stacks T A := {S1 with R := Function.update S1.R cursor (List.replicate (n-W) tick)}
  have he2' : Exec body (usub band cursor tmp) (mk v1 S1) (4*(W)+4) (mk v2 S2) := by
    simpa [S2,S1,hn,hW,hfresh cursor (by simp),hfresh count (by simp),hfresh tmp (by simp),‹index ≠ band›,‹index ≠ band›.symm,‹index ≠ cursor›,‹index ≠ cursor›.symm,‹index ≠ count›,‹index ≠ count›.symm,‹index ≠ tmp›,‹index ≠ tmp›.symm,‹band ≠ cursor›,‹band ≠ cursor›.symm,‹band ≠ count›,‹band ≠ count›.symm,‹band ≠ tmp›,‹band ≠ tmp›.symm,‹cursor ≠ count›,‹cursor ≠ count›.symm,‹cursor ≠ tmp›,‹cursor ≠ tmp›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm,List.drop_replicate,Action.run,update_rt,List.replicate_succ] using he2
  obtain ⟨v3,hu3,he3⟩ := ucopy_exec body (a := index) (b := count) (t := tmp)
    ‹index ≠ count› ‹index ≠ tmp› ‹count ≠ tmp› v2 S2 (by simpa [S2,S1,hn,hW,hfresh cursor (by simp),hfresh count (by simp),hfresh tmp (by simp),‹index ≠ band›,‹index ≠ band›.symm,‹index ≠ cursor›,‹index ≠ cursor›.symm,‹index ≠ count›,‹index ≠ count›.symm,‹index ≠ tmp›,‹index ≠ tmp›.symm,‹band ≠ cursor›,‹band ≠ cursor›.symm,‹band ≠ count›,‹band ≠ count›.symm,‹band ≠ tmp›,‹band ≠ tmp›.symm,‹cursor ≠ count›,‹cursor ≠ count›.symm,‹cursor ≠ tmp›,‹cursor ≠ tmp›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm] using hfresh tmp (by simp))
  let S3 : Stacks T A := {S2 with R := Function.update S2.R count (List.replicate (n) tick)}
  have he3' : Exec body (ucopy index count tmp) (mk v2 S2) (4*(n)+4) (mk v3 S3) := by
    simpa [S3,S2,S1,hn,hW,hfresh cursor (by simp),hfresh count (by simp),hfresh tmp (by simp),‹index ≠ band›,‹index ≠ band›.symm,‹index ≠ cursor›,‹index ≠ cursor›.symm,‹index ≠ count›,‹index ≠ count›.symm,‹index ≠ tmp›,‹index ≠ tmp›.symm,‹band ≠ cursor›,‹band ≠ cursor›.symm,‹band ≠ count›,‹band ≠ count›.symm,‹band ≠ tmp›,‹band ≠ tmp›.symm,‹cursor ≠ count›,‹cursor ≠ count›.symm,‹cursor ≠ tmp›,‹cursor ≠ tmp›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm,List.drop_replicate,Action.run,update_rt,List.replicate_succ] using he3
  obtain ⟨v4,hu4,he4⟩ := ucopy_exec body (a := band) (b := count) (t := tmp)
    ‹band ≠ count› ‹band ≠ tmp› ‹count ≠ tmp› v3 S3 (by simpa [S3,S2,S1,hn,hW,hfresh cursor (by simp),hfresh count (by simp),hfresh tmp (by simp),‹index ≠ band›,‹index ≠ band›.symm,‹index ≠ cursor›,‹index ≠ cursor›.symm,‹index ≠ count›,‹index ≠ count›.symm,‹index ≠ tmp›,‹index ≠ tmp›.symm,‹band ≠ cursor›,‹band ≠ cursor›.symm,‹band ≠ count›,‹band ≠ count›.symm,‹band ≠ tmp›,‹band ≠ tmp›.symm,‹cursor ≠ count›,‹cursor ≠ count›.symm,‹cursor ≠ tmp›,‹cursor ≠ tmp›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm] using hfresh tmp (by simp))
  let S4 : Stacks T A := {S3 with R := Function.update S3.R count (List.replicate (n+W) tick)}
  have he4' : Exec body (ucopy band count tmp) (mk v3 S3) (4*(W)+4) (mk v4 S4) := by
    simpa [S4,S3,S2,S1,hn,hW,hfresh cursor (by simp),hfresh count (by simp),hfresh tmp (by simp),‹index ≠ band›,‹index ≠ band›.symm,‹index ≠ cursor›,‹index ≠ cursor›.symm,‹index ≠ count›,‹index ≠ count›.symm,‹index ≠ tmp›,‹index ≠ tmp›.symm,‹band ≠ cursor›,‹band ≠ cursor›.symm,‹band ≠ count›,‹band ≠ count›.symm,‹band ≠ tmp›,‹band ≠ tmp›.symm,‹cursor ≠ count›,‹cursor ≠ count›.symm,‹cursor ≠ tmp›,‹cursor ≠ tmp›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm,List.drop_replicate,Action.run,update_rt,List.replicate_succ] using he4
  have he5 := Exec.act (body := body) (.push (.rt count) (fun _ => tick) .done) (mk v4 S4)
  let v5 := v4
  have hu5 : v5.user = v4.user := rfl
  let S5 : Stacks T A := {S4 with R := Function.update S4.R count (List.replicate (n+W+1) tick)}
  have he5' : Exec body (.act (.push (.rt count) (fun _ => tick) .done)) (mk v4 S4) (1) (mk v5 S5) := by
    simpa [S5,S4,S3,S2,S1,hn,hW,hfresh cursor (by simp),hfresh count (by simp),hfresh tmp (by simp),‹index ≠ band›,‹index ≠ band›.symm,‹index ≠ cursor›,‹index ≠ cursor›.symm,‹index ≠ count›,‹index ≠ count›.symm,‹index ≠ tmp›,‹index ≠ tmp›.symm,‹band ≠ cursor›,‹band ≠ cursor›.symm,‹band ≠ count›,‹band ≠ count›.symm,‹band ≠ tmp›,‹band ≠ tmp›.symm,‹cursor ≠ count›,‹cursor ≠ count›.symm,‹cursor ≠ tmp›,‹cursor ≠ tmp›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm,List.drop_replicate,Action.run,update_rt,List.replicate_succ] using he5
  refine ⟨v5,hu5.trans (hu4.trans (hu3.trans (hu2.trans (hu1)))),(Exec.seq he1' (Exec.seq he2' (Exec.seq he3' (Exec.seq he4' (he5'))))).cast (by simp [bandIntervalEndpointsCost]) ?_⟩
  apply congrArg (mk v5)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hc : k = cursor <;> by_cases hn : k = count <;>
    simp_all [S5,S4,S3,S2,S1]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
