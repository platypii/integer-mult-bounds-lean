module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Advance an ambient stream by one row while retaining both its forward
working copy and its reversed restoration archive. Each source symbol is
visited a constant number of times, independently of its replica index. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def takeCopyPrefix (count src dst archive saved tmp : Fin T) : Pr P T Q A U :=
  .seq (copyPrefix count src dst saved tmp) (transfer count src archive tmp)

theorem takeCopyPrefix_exec (count src dst archive saved tmp : Fin T)
    (hreg : [count,src,dst,archive,saved,tmp].Nodup)
    (xs tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = xs.length) (hsrc : S.R src = xs++tail)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (takeCopyPrefix count src dst archive saved tmp) (Host.mk v S) (14*xs.length+14)
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R src tail)
          dst (xs++S.R dst)) archive (xs.reverse++S.R archive))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyPrefix_exec (body := body)
    (count := count) (src := src) (dst := dst) (saved := saved) (tmp := tmp)
    (by regs_nodup) v S xs tail hsrc hcount hsaved htmp
  let H : Stacks T A := {S with R := Function.update S.R dst (xs++S.R dst)}
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body)
    (count := count) (src := src) (dst := archive) (tmp := tmp) (by regs_nodup) v₁ H xs tail
    (by simpa [H,‹src ≠ dst›] using hsrc)
    (by simpa [H,‹count ≠ dst›] using hcount)
    (by simpa [H,‹dst ≠ tmp›.symm] using htmp)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast (by omega) ?_⟩
  apply congrArg (Host.mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hiSrc : i = src <;> by_cases hiDst : i = dst <;> by_cases hiArchive : i = archive <;>
    simp [H,hiSrc,hiDst,hiArchive,‹src ≠ dst›,‹src ≠ archive›,‹dst ≠ archive›,
      ‹src ≠ dst›.symm,‹dst ≠ archive›.symm]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
