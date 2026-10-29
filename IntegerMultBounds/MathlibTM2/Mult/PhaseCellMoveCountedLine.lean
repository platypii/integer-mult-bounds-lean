module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTransferCountedLine

/-! Move an owned line prefix in natural order, restoring its generated clock
and reversal workspace and leaving an arbitrary borrowed source suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def moveCountedLine (rows width src dst rev count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (transferCountedLine rows width src rev count saved tmp) (moveR rev dst id)

def moveCountedLineCost (n w : ℕ) : ℕ := n*(12*w+9)+12

theorem moveCountedLine_exec (rows width src dst rev count saved tmp : Fin T)
    (hreg : [rows,width,src,dst,rev,count,saved,tmp].Nodup) (n w : ℕ)
    (words tail : List (Fin (A+4))) (hlen : words.length = n*w)
    (v : HS T Q A U) (S : Stacks T A)
    (hn : (S.R rows).length = n) (hw : (S.R width).length = w)
    (hsrc : S.R src = words++tail) (hrev : S.R rev = [])
    (hcount : S.R count = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ moveCountedLineCost n w ∧
      Exec body (moveCountedLine rows width src dst rev count saved tmp) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R src tail) dst (words++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  have ht : [rows,width,src,rev,count,saved,tmp].Nodup := by simp_all
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := transferCountedLine_exec (body := body)
    rows width src rev count saved tmp ht n w words tail hlen v S hn hw hsrc hcount hsaved htmp
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R src tail) rev words.reverse)}
  have he₁' : Exec body (transferCountedLine rows width src rev count saved tmp) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [S₁,hrev,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body rev dst ‹dst ≠ rev›.symm id v₁ S₁
  refine ⟨v₂,m₁+(2*words.length+2),hu₂.trans hu₁,?_,(Exec.seq he₁' he₂).cast (by simp [S₁]) ?_⟩
  · dsimp only [moveCountedLineCost,transferCountedLineCost] at *
    rw [hlen]
    nlinarith only [hm₁]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hs : k = src
    · subst k; simp [S₁,movedR,‹src ≠ rev›,‹src ≠ dst›]
    by_cases hd : k = dst
    · subst k; simp [S₁,movedR,hs,‹dst ≠ rev›]
    by_cases hv : k = rev
    · subst k; simp [S₁,movedR,hd,‹src ≠ rev›.symm,hrev]
    · simp [S₁,movedR,hs,hd,hv]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
