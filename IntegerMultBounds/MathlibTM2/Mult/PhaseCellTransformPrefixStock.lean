module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTransformPrefix
public import IntegerMultBounds.MathlibTM2.Host.BinArithStock
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget

/-! Prefix routing composes a local storage trace without charging its running time. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Instantiate the local transformation with an actual restoring execution.
Only its input and output lengths enter the routing charge. -/
theorem transformPrefix_exec_within {count src work saved tmp : Fin T}
    (hreg : [count,src,work,saved,tmp].Nodup) (run : Pr P T Q A U)
    (xs ys tail : List (Fin (A+4))) (cost workspace : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = xs++tail) (hcount : (S.R count).length = xs.length)
    (hwork : S.R work = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hrun : ∀ v : HS T Q A U, ∃ v' n, v'.user = v.user ∧ n ≤ cost ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (isolatedPrefixState S src work saved xs tail))+0+workspace) 0
        run (mk v (isolatedPrefixState S src work saved xs tail)) n
        (mk v' {(isolatedPrefixState S src work saved xs tail) with R :=
          (Function.update (isolatedPrefixState S src work saved xs tail).R work ys)})) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cost+6*xs.length+4*ys.length+10 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        ((8*xs.length+8)+workspace)) 0
        (transformPrefix count src work saved tmp run) (mk v S) n
        (mk v' {S with R := Function.update S.R src (ys++tail)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body)
    (show [count,src,saved,tmp].Nodup by regs_nodup) v S xs tail hsrc hcount htmp
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R src tail) saved xs.reverse)}
  have he₁' : Exec body (transfer count src saved tmp) (mk v S) (4*xs.length+4) (mk v₁ S₁) := by
    simpa [S₁,hsaved] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (body := body) saved work ‹work ≠ saved›.symm id v₁ S₁
  let S₂ := isolatedPrefixState S src work saved xs tail
  have he₂' : Exec body (moveR saved work id) (mk v₁ S₁) (2*xs.length+2) (mk v₂ S₂) := by
    simpa [S₂,S₁,isolatedPrefixState,movedR,‹src ≠ work›.symm,‹work ≠ saved›,hwork] using he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,hw₃⟩ := hrun v₂
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R work ys}
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec (body := body) work tmp ‹work ≠ tmp› id v₃ S₃
  let S₄ : Stacks T A := {S₃ with R := movedR S₃.R work tmp id (S₃.R work)}
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec (body := body) tmp src ‹src ≠ tmp›.symm id v₄ S₄
  have h₃work : S₃.R work = ys := by simp [S₃]
  have h₃tmp : S₃.R tmp = [] := by
    simp [S₃,S₂,isolatedPrefixState,‹work ≠ tmp›.symm,‹saved ≠ tmp›.symm,‹src ≠ tmp›.symm,htmp]
  have h₄tmp : S₄.R tmp = ys.reverse := by simp [S₄,movedR,h₃work,h₃tmp]
  have hw₁ := mn_native_exec_within he₁' 2 (by
    simp [transfer,scanR,drainR,popDo,keepIn,transferAct,moveR,moveStep,whileR,peekR,
      mnNativePushBound,mnActPush]) 0 (mnSize (mk v S)+0+(8*xs.length+8)) (by omega)
  have hw₂ := moveR_within saved work id he₂' 0 _ hw₁.final
  have hw₄ := moveR_within work tmp id he₄ 0 _ hw₃.final
  have hw₅ := moveR_within tmp src id he₅ 0 _ hw₄.final
  have hwPrep := ExecWithin.seq hw₁ hw₂
  have hwPost := ExecWithin.seq hw₃ (ExecWithin.seq hw₄ hw₅)
  have hwWhole := execWithin_seq_two_budget body _ _ _ _ _ _ _ 0 _ _ hwPrep hwPost
  refine ⟨v₅,(4*xs.length+4)+(2*xs.length+2)+n₃+(2*ys.length+2)+(2*ys.length+2),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),by omega,
    hwWhole.seq_assoc.cast ?_ ?_⟩
  · simp [h₃work,h₄tmp,Nat.add_assoc]
  · apply congrArg (mk v₅)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hs : i = src
    · subst i; simp [S₄,S₃,S₂,isolatedPrefixState,movedR,Function.update_apply, *, Ne.symm]
    by_cases hw : i = work
    · subst i; simp [S₄,S₃,S₂,isolatedPrefixState,movedR,Function.update_apply, *, Ne.symm]
    by_cases hb : i = saved
    · subst i; simp [S₄,S₃,S₂,isolatedPrefixState,movedR,Function.update_apply, *, Ne.symm]
    by_cases ht : i = tmp
    · subst i; simp [S₄,S₃,S₂,isolatedPrefixState,movedR,Function.update_apply, *, Ne.symm]
    · simp [S₄,S₃,S₂,isolatedPrefixState,movedR,Function.update_apply,hs,hw,hb,ht]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
