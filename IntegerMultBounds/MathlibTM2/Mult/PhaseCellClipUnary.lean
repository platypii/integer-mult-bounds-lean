module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Clip an owned unary count to a borrowed unary bound and restore both scratch tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def clipUnary (total count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (ucopy total saved tmp) (.seq (usub count saved tmp) (.seq (uclear count) (.seq (ucopy total count tmp) (.seq (usub saved count tmp) (uclear saved)))))

def clipUnaryCost (N x : ℕ) : ℕ :=
  [4*(N)+4,4*(x)+4,2*(x)+2,4*(N)+4,4*(N-x)+4,2*(N-x)+2].sum

theorem clipUnary_exec {total count saved tmp : Fin T}
    (hreg : [total,count,saved,tmp].Nodup) (N x : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R total).length = N) (hx : (S.R count).length = x)
    (hcount : S.R count = List.replicate x tick)
    (hfresh : ∀ k ∈ [saved,tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (clipUnary total count saved tmp) (mk v S)
        (clipUnaryCost N x)
        (mk v' {S with R := Function.update S.R count (List.replicate (min N x) tick)}) := by
  have hr := hreg
  regs_ne hr
  have hclip : N-(N-x) = min N x := by omega
  obtain ⟨v1,hu1,he1⟩ := ucopy_exec body (a := total) (b := saved) (t := tmp)
    ‹total ≠ saved› ‹total ≠ tmp› ‹saved ≠ tmp› v S (by simpa [hN,hx,hcount,hclip,hfresh saved (by simp),hfresh tmp (by simp),‹total ≠ count›,‹total ≠ count›.symm,‹total ≠ saved›,‹total ≠ saved›.symm,‹total ≠ tmp›,‹total ≠ tmp›.symm,‹count ≠ saved›,‹count ≠ saved›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,‹saved ≠ tmp›,‹saved ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm] using hfresh tmp (by simp))
  let S1 : Stacks T A := {S with R := Function.update S.R saved (List.replicate (N) tick)}
  have he1' : Exec body (ucopy total saved tmp) (mk v S) (4*(N)+4) (mk v1 S1) := by
    simpa [S1,hN,hx,hcount,hclip,hfresh saved (by simp),hfresh tmp (by simp),‹total ≠ count›,‹total ≠ count›.symm,‹total ≠ saved›,‹total ≠ saved›.symm,‹total ≠ tmp›,‹total ≠ tmp›.symm,‹count ≠ saved›,‹count ≠ saved›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,‹saved ≠ tmp›,‹saved ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm,List.drop_replicate,Action.run,update_rt,List.replicate_succ] using he1
  obtain ⟨v2,hu2,he2⟩ := usub_exec body (a := count) (b := saved) (t := tmp)
    ‹count ≠ saved› ‹count ≠ tmp› ‹saved ≠ tmp› v1 S1 (by simpa [S1,hN,hx,hcount,hclip,hfresh saved (by simp),hfresh tmp (by simp),‹total ≠ count›,‹total ≠ count›.symm,‹total ≠ saved›,‹total ≠ saved›.symm,‹total ≠ tmp›,‹total ≠ tmp›.symm,‹count ≠ saved›,‹count ≠ saved›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,‹saved ≠ tmp›,‹saved ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm] using hfresh tmp (by simp))
  let S2 : Stacks T A := {S1 with R := Function.update S1.R saved (List.replicate (N-x) tick)}
  have he2' : Exec body (usub count saved tmp) (mk v1 S1) (4*(x)+4) (mk v2 S2) := by
    simpa [S2,S1,hN,hx,hcount,hclip,hfresh saved (by simp),hfresh tmp (by simp),‹total ≠ count›,‹total ≠ count›.symm,‹total ≠ saved›,‹total ≠ saved›.symm,‹total ≠ tmp›,‹total ≠ tmp›.symm,‹count ≠ saved›,‹count ≠ saved›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,‹saved ≠ tmp›,‹saved ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm,List.drop_replicate,Action.run,update_rt,List.replicate_succ] using he2
  obtain ⟨v3,hu3,he3⟩ := uclear_exec body count v2 S2
  let S3 : Stacks T A := {S2 with R := Function.update S2.R count ([])}
  have he3' : Exec body (uclear count) (mk v2 S2) (2*(x)+2) (mk v3 S3) := by
    simpa [S3,S2,S1,hN,hx,hcount,hclip,hfresh saved (by simp),hfresh tmp (by simp),‹total ≠ count›,‹total ≠ count›.symm,‹total ≠ saved›,‹total ≠ saved›.symm,‹total ≠ tmp›,‹total ≠ tmp›.symm,‹count ≠ saved›,‹count ≠ saved›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,‹saved ≠ tmp›,‹saved ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm,List.drop_replicate,Action.run,update_rt,List.replicate_succ] using he3
  obtain ⟨v4,hu4,he4⟩ := ucopy_exec body (a := total) (b := count) (t := tmp)
    ‹total ≠ count› ‹total ≠ tmp› ‹count ≠ tmp› v3 S3 (by simpa [S3,S2,S1,hN,hx,hcount,hclip,hfresh saved (by simp),hfresh tmp (by simp),‹total ≠ count›,‹total ≠ count›.symm,‹total ≠ saved›,‹total ≠ saved›.symm,‹total ≠ tmp›,‹total ≠ tmp›.symm,‹count ≠ saved›,‹count ≠ saved›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,‹saved ≠ tmp›,‹saved ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm] using hfresh tmp (by simp))
  let S4 : Stacks T A := {S3 with R := Function.update S3.R count (List.replicate (N) tick)}
  have he4' : Exec body (ucopy total count tmp) (mk v3 S3) (4*(N)+4) (mk v4 S4) := by
    simpa [S4,S3,S2,S1,hN,hx,hcount,hclip,hfresh saved (by simp),hfresh tmp (by simp),‹total ≠ count›,‹total ≠ count›.symm,‹total ≠ saved›,‹total ≠ saved›.symm,‹total ≠ tmp›,‹total ≠ tmp›.symm,‹count ≠ saved›,‹count ≠ saved›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,‹saved ≠ tmp›,‹saved ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm,List.drop_replicate,Action.run,update_rt,List.replicate_succ] using he4
  obtain ⟨v5,hu5,he5⟩ := usub_exec body (a := saved) (b := count) (t := tmp)
    ‹count ≠ saved›.symm ‹saved ≠ tmp› ‹count ≠ tmp› v4 S4 (by simpa [S4,S3,S2,S1,hN,hx,hcount,hclip,hfresh saved (by simp),hfresh tmp (by simp),‹total ≠ count›,‹total ≠ count›.symm,‹total ≠ saved›,‹total ≠ saved›.symm,‹total ≠ tmp›,‹total ≠ tmp›.symm,‹count ≠ saved›,‹count ≠ saved›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,‹saved ≠ tmp›,‹saved ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm] using hfresh tmp (by simp))
  let S5 : Stacks T A := {S4 with R := Function.update S4.R count (List.replicate (min N x) tick)}
  have he5' : Exec body (usub saved count tmp) (mk v4 S4) (4*(N-x)+4) (mk v5 S5) := by
    simpa [S5,S4,S3,S2,S1,hN,hx,hcount,hclip,hfresh saved (by simp),hfresh tmp (by simp),‹total ≠ count›,‹total ≠ count›.symm,‹total ≠ saved›,‹total ≠ saved›.symm,‹total ≠ tmp›,‹total ≠ tmp›.symm,‹count ≠ saved›,‹count ≠ saved›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,‹saved ≠ tmp›,‹saved ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm,List.drop_replicate,Action.run,update_rt,List.replicate_succ] using he5
  obtain ⟨v6,hu6,he6⟩ := uclear_exec body saved v5 S5
  let S6 : Stacks T A := {S5 with R := Function.update S5.R saved ([])}
  have he6' : Exec body (uclear saved) (mk v5 S5) (2*(N-x)+2) (mk v6 S6) := by
    simpa [S6,S5,S4,S3,S2,S1,hN,hx,hcount,hclip,hfresh saved (by simp),hfresh tmp (by simp),‹total ≠ count›,‹total ≠ count›.symm,‹total ≠ saved›,‹total ≠ saved›.symm,‹total ≠ tmp›,‹total ≠ tmp›.symm,‹count ≠ saved›,‹count ≠ saved›.symm,‹count ≠ tmp›,‹count ≠ tmp›.symm,‹saved ≠ tmp›,‹saved ≠ tmp›.symm,List.replicate_append_replicate,Nat.add_comm,List.drop_replicate,Action.run,update_rt,List.replicate_succ] using he6
  refine ⟨v6,hu6.trans (hu5.trans (hu4.trans (hu3.trans (hu2.trans (hu1))))),(Exec.seq he1' (Exec.seq he2' (Exec.seq he3' (Exec.seq he4' (Exec.seq he5' (he6')))))).cast (by simp [clipUnaryCost]) ?_⟩
  apply congrArg (mk v6)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hn : k = count <;> by_cases hs : k = saved <;>
    simp_all [S6,S5,S4,S3,S2,S1,hfresh saved (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
