module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseHaloGroupHeaders

/-! Empty halo classes release private endpoint and ordinary header copies,
leaving retained endpoints, parameters and ambient payloads untouched. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}

def releaseEmptyHaloGroup : Pr P 144 Q A U :=
  .seq releaseHaloGroupHeaders (uclear 128)

theorem releaseEmptyHaloGroup_exec (P N q l s t u band a b L : ℕ)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hfresh : ∀ r ∈ groupHeaderCopies, S.R r.2 = [])
    (h111 : S.R 111 = []) (h113 : S.R 113 = []) (h128 : (S.R 128).length = L) :
    ∃ v', v'.user = v.user ∧
      Exec body releaseEmptyHaloGroup (mk v { S with R := copiedHaloGroupR P N q l s t u band a b L S.R })
        (2*(P+N+q+l+s+t+u+band+3*L+a+b)+28) (mk v' { S with R := Function.update S.R 128 [] }) := by
  obtain ⟨v₁,hu₁,he₁⟩ := releaseHaloGroupHeaders_exec (body := body)
    P N q l s t u band a b L v S hfresh h111 h113
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body 128 v₁ S
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ rfl⟩
  rw [h128]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
