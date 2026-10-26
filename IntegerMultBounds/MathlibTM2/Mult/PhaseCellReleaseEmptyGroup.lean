module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseGroupHeaders

/-! An empty class releases its private header copies and current outer length.
The ambient source, output and pending key metadata are restored exactly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}

def releaseEmptyGroup : Pr P 144 Q A U := .seq releaseGroupHeaders (uclear 128)

theorem releaseEmptyGroup_exec (P N q l s t u band L : ℕ) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hfresh : ∀ r ∈ groupHeaderCopies, S.R r.2 = []) (h128 : (S.R 128).length = L) :
    ∃ v', v'.user = v.user ∧
      Exec body releaseEmptyGroup (mk v { S with R := copiedGroupR P N q l s t u band L S.R })
        (2*(P+N+q+l+s+t+u+band+3*L)+23) (mk v' { S with R := Function.update S.R 128 [] }) := by
  obtain ⟨v₁,hu₁,he₁⟩ := releaseGroupHeaders_exec (body144 := body) P N q l s t u band L v S hfresh
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body 128 v₁ S
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ rfl⟩
  rw [h128]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
