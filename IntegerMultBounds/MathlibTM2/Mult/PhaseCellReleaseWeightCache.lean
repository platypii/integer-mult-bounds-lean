module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWeightCache
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix

/-! Release the owned weight page and replay clock while preserving a borrowed cache suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 121 Q A U}

def releaseWeightCache : Pr P 121 Q A U :=
  .seq (discardPrefix 118 117 119 120) (uclear 118)

theorem releaseWeightCache_exec (v : HS 121 Q A U) (S : Stacks 121 A)
    (page tail : List (Fin (A+4))) (n : ℕ) (hlen : page.length = 2*n)
    (hpage : S.R 117 = page++tail) (hcount : (S.R 118).length = 2*n)
    (h119 : S.R 119 = []) (h120 : S.R 120 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body releaseWeightCache (mk v S) (16*n+8)
        (mk v' {S with R := (Function.update (Function.update S.R 117 tail) 118 [])}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := discardPrefix_exec (body := body)
    (show [(118 : Fin 121),117,119,120].Nodup by decide) page tail v S hpage
    (hcount.trans hlen.symm) h119 h120
  let M : Stacks 121 A := {S with R := Function.update S.R 117 tail}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec (body := body) 118 v₁ M
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ rfl⟩
  simp only [M,Function.update_of_ne (show (118 : Fin 121) ≠ 117 by decide),hlen,hcount]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
