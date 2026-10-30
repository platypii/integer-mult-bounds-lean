module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Isolate, transform and return an owned prefix without scanning its suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def isolatedPrefixState (S : Stacks T A) (src work saved : Fin T)
    (xs tail : List (Fin (A+4))) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update S.R src tail) saved []) work xs)}

def transformPrefix (count src work saved tmp : Fin T) (run : Pr P T Q A U) : Pr P T Q A U :=
  .seq (transfer count src saved tmp)
    (.seq (moveR saved work id) (.seq run (.seq (moveR work tmp id) (moveR tmp src id))))

/-- Instantiate the local transformation with an actual restoring execution.
Only its input and output lengths enter the routing charge. -/
theorem transformPrefix_exec {count src work saved tmp : Fin T}
    (hreg : [count,src,work,saved,tmp].Nodup) (run : Pr P T Q A U)
    (xs ys tail : List (Fin (A+4))) (cost : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = xs++tail) (hcount : (S.R count).length = xs.length)
    (hwork : S.R work = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hrun : ∀ v : HS T Q A U, ∃ v' n, v'.user = v.user ∧ n ≤ cost ∧
      Exec body run (mk v (isolatedPrefixState S src work saved xs tail)) n
        (mk v' {(isolatedPrefixState S src work saved xs tail) with R :=
          (Function.update (isolatedPrefixState S src work saved xs tail).R work ys)})) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cost+6*xs.length+4*ys.length+10 ∧
      Exec body (transformPrefix count src work saved tmp run) (mk v S) n
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
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := hrun v₂
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R work ys}
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec (body := body) work tmp ‹work ≠ tmp› id v₃ S₃
  let S₄ : Stacks T A := {S₃ with R := movedR S₃.R work tmp id (S₃.R work)}
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec (body := body) tmp src ‹src ≠ tmp›.symm id v₄ S₄
  have h₃work : S₃.R work = ys := by simp [S₃]
  have h₃tmp : S₃.R tmp = [] := by
    simp [S₃,S₂,isolatedPrefixState,‹work ≠ tmp›.symm,‹saved ≠ tmp›.symm,‹src ≠ tmp›.symm,htmp]
  have h₄tmp : S₄.R tmp = ys.reverse := by simp [S₄,movedR,h₃work,h₃tmp]
  refine ⟨v₅,(4*xs.length+4)+(2*xs.length+2)+n₃+(2*ys.length+2)+(2*ys.length+2),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),by omega,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast ?_ ?_⟩
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
