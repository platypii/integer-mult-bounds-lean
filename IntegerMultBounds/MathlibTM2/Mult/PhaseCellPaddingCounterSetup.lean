module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate a padding-symbol counter from retained row and block dimensions.
The subtraction workspace is retired before returning to the caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def paddingCounterSetup (rows capacity width padding missing saved tmp : Fin T) : Pr P T Q A U :=
  .seq (ucopy capacity missing saved)
    (.seq (usub rows missing tmp)
      (.seq (unaryProduct missing width padding saved tmp) (uclear missing)))

theorem paddingCounterSetup_exec (rows capacity width padding missing saved tmp : Fin T)
    (hreg : [rows,capacity,width,padding,missing,saved,tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hpadding : S.R padding = []) (hmissing : S.R missing = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 4*(S.R capacity).length+4 + (4*(S.R rows).length+4) +
        (((S.R capacity).length-(S.R rows).length)*(4*(S.R width).length+9)+4) +
        (2*((S.R capacity).length-(S.R rows).length)+2) ∧
      Exec body (paddingCounterSetup rows capacity width padding missing saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R padding
          (List.replicate (((S.R capacity).length-(S.R rows).length)*(S.R width).length) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body ‹capacity ≠ missing› ‹capacity ≠ saved› ‹missing ≠ saved› v S hsaved
  let S₁ : Stacks T A := {S with R := (Function.update S.R missing
    (List.replicate (S.R capacity).length tick))}
  have he₁' : Exec body (ucopy capacity missing saved) (Host.mk v S)
      (4*(S.R capacity).length+4) (Host.mk v₁ S₁) := by
    simpa only [hmissing,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := usub_exec body ‹rows ≠ missing› ‹rows ≠ tmp› ‹missing ≠ tmp› v₁ S₁
    (by simp [S₁,htmp,‹missing ≠ tmp›.symm])
  let S₂ : Stacks T A := {S with R := (Function.update S.R missing
    (List.replicate ((S.R capacity).length-(S.R rows).length) tick))}
  have he₂' : Exec body (usub rows missing tmp) (Host.mk v₁ S₁)
      (4*(S.R rows).length+4) (Host.mk v₂ S₂) := by
    simpa [S₁,S₂,‹rows ≠ missing›] using he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := unaryProduct_exec (body := body)
    (a := missing) (b := width) (dst := padding) (t₁ := saved) (t₂ := tmp)
    (by regs_nodup) v₂ S₂
    (by simp [S₂,hsaved,‹missing ≠ saved›.symm])
    (by simp [S₂,htmp,‹missing ≠ tmp›.symm])
  let S₃ : Stacks T A := {S₂ with R := (Function.update S₂.R padding
    (List.replicate (((S.R capacity).length-(S.R rows).length)*(S.R width).length) tick))}
  have he₃' : Exec body (unaryProduct missing width padding saved tmp)
      (Host.mk v₂ S₂) n₃ (Host.mk v₃ S₃) := by
    simpa [S₂,S₃,‹width ≠ missing›,‹padding ≠ missing›,hpadding] using he₃
  have hn₃' : n₃ ≤ ((S.R capacity).length-(S.R rows).length)*(4*(S.R width).length+9)+4 := by
    simpa [S₂,‹width ≠ missing›] using hn₃
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) missing v₃ S₃
  have he₄' : Exec body (uclear missing) (Host.mk v₃ S₃)
      (2*((S.R capacity).length-(S.R rows).length)+2)
      (Host.mk v₄ {S with R := (Function.update S.R padding
        (List.replicate (((S.R capacity).length-(S.R rows).length)*(S.R width).length) tick))}) := by
    have hend : {S₃ with R := Function.update S₃.R missing []} =
        {S with R := (Function.update S.R padding
          (List.replicate (((S.R capacity).length-(S.R rows).length)*(S.R width).length) tick))} := by
      congr 1
      funext k
      by_cases hk : k = missing
      · subst k
        simp [S₃,S₂,‹padding ≠ missing›.symm,hmissing]
      · by_cases hp : k = padding <;> simp [S₃,S₂,hk,hp,‹padding ≠ missing›]
    rw [hend] at he₄
    simpa [S₃,S₂,‹padding ≠ missing›.symm] using he₄
  refine ⟨v₄,_,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄'))⟩
  · omega
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
