module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Increment one fixed-width binary packet field, preserving its suffix and all controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def advanceBinaryPacket (width src word saved tmp cy : Fin T) : Pr P T Q A U :=
  .seq (takePrefix width src word saved tmp)
    (.seq (countIter word saved cy) (.seq (moveR word tmp id) (moveR tmp src id)))

theorem advanceBinaryPacket_exec (width src word saved tmp cy : Fin T)
    (hreg : [width,src,word,saved,tmp].Nodup) (W x : ℕ) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = W) (hsrc : S.R src = binSyms W x++tail)
    (hword : S.R word = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (advanceBinaryPacket width src word saved tmp cy) (mk v S) (14*W+15)
        (mk v' {S with R := Function.update S.R src (binSyms W (x+1)++tail)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec (body := body) hreg v S (binSyms W x) tail
    hsrc (by simpa using hwidth) hsaved htmp
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R src tail) word (binSyms W x))}
  have he₁' : Exec body (takePrefix width src word saved tmp) (mk v S) (6*W+6) (mk v₁ S₁) := by
    simpa [S₁,hword] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := countIter_exec body (W := W) (j := x) ‹word ≠ saved› cy v₁ S₁ (by simp [S₁])
    (by simpa [S₁,‹word ≠ saved›.symm,‹src ≠ saved›.symm] using hsaved)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R word (binSyms W (x+1))}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body word tmp ‹word ≠ tmp› id v₂ S₂
  let S₃ : Stacks T A := {S₂ with R := movedR S₂.R word tmp id (S₂.R word)}
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec body tmp src ‹src ≠ tmp›.symm id v₃ S₃
  refine ⟨v₄,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · simp [S₃,S₂,S₁,movedR,‹word ≠ tmp›.symm,‹src ≠ tmp›.symm,htmp]
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    have hts : tmp ≠ src := ‹src ≠ tmp›.symm
    have htw : tmp ≠ word := ‹word ≠ tmp›.symm
    have hws : word ≠ src := ‹src ≠ word›.symm
    funext k
    by_cases hs : k = src <;> by_cases hw : k = word <;> by_cases ht : k = tmp <;>
      simp_all [S₃,S₂,S₁,movedR]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
