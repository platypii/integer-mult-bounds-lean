module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Consume one row-counted packed line while restoring all private controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def takeCountedLine (rows width src dst count buf tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct rows width count buf tmp)
    (.seq (takePrefix count src dst buf tmp) (uclear count))

def takeCountedLineCost (rows width : ℕ) : ℕ := rows*(12*width+9)+12

theorem takeCountedLine_exec {rows width src dst count buf tmp : Fin T}
    (hreg : [rows,width,src,dst,count,buf,tmp].Nodup) (s w : ℕ)
    (xs tail : List (Fin (A+4))) (hlen : xs.length = s*w)
    (v : HS T Q A U) (S : Stacks T A)
    (hs : (S.R rows).length = s) (hw : (S.R width).length = w)
    (hsource : S.R src = xs++tail)
    (hcount : S.R count = []) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ takeCountedLineCost s w ∧
      Exec body (takeCountedLine rows width src dst count buf tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src tail) dst (xs++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := rows) (b := width) (dst := count) (t₁ := buf) (t₂ := tmp)
    (by regs_nodup) v S hbuf htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R count (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct rows width count buf tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hs,hw,hcount,List.append_nil] using he₁
  have hn₁' : n₁ ≤ s*(4*w+9)+4 := by simpa only [hs,hw] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := takePrefix_exec (body := body)
    (count := count) (src := src) (dst := dst) (buf := buf) (tmp := tmp)
    (by regs_nodup) v₁ S₁ xs tail (by simpa [S₁, ‹src ≠ count›] using hsource)
    (by simp [S₁, hlen]) (by simpa [S₁, ‹count ≠ buf›.symm] using hbuf)
    (by simpa [S₁, ‹count ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S₁ with R := (Function.update (Function.update S₁.R src tail) dst (xs++S₁.R dst))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body count v₂ S₂
  have hclock : (S₂.R count).length = s*w := by
    simp [S₂, S₁, ‹dst ≠ count›.symm, ‹src ≠ count›.symm]
  refine ⟨v₃,n₁+((6*xs.length+6)+(2*(S₂.R count).length+2)),
    hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hlen,hclock]
    unfold takeCountedLineCost
    nlinarith only [hn₁']
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hsrc : i = src <;> by_cases hdst : i = dst <;> by_cases hc : i = count <;>
      simp_all [S₂, S₁, Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
