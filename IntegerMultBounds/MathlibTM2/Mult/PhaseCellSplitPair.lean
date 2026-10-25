module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream

/-! Consume one interleaved pair into separate word banks, preserving bit order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def splitPair : Pr P₀ 117 Q A U :=
  .seq (takePrefix 94 110 111 104 105) (takePrefix 94 110 113 104 105)

theorem splitPair_exec (w : ℕ) (x y : GaussianInt) (v : HS 117 Q A U) (S : Stacks 117 A)
    (tail : List (Fin (A + 4))) (hw : (S.R 94).length = w)
    (hsrc : S.R 110 = csyms A w x ++ (csyms A w y ++ tail))
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v', v'.user = v.user ∧ Exec body splitPair (mk v S) (12 * w + 12)
      (mk v' { S with R := (Function.update (Function.update (Function.update S.R 110 tail)
        111 (csyms A w x ++ S.R 111)) 113 (csyms A w y ++ S.R 113)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := takePrefix_exec (body := body)
    (show [(94 : Fin 117), 110, 111, 104, 105].Nodup by decide) v S
    (csyms A w x) (csyms A w y ++ tail) hsrc (by simpa using hw) h104 h105
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update S.R 110
    (csyms A w y ++ tail)) 111 (csyms A w x ++ S.R 111)) }
  obtain ⟨v₂, hu₂, he₂⟩ := takePrefix_exec (body := body)
    (show [(94 : Fin 117), 110, 113, 104, 105].Nodup by decide) v₁ S₁
    (csyms A w y) tail (by simp [S₁]) (by simpa [S₁] using hw)
    (by simpa [S₁] using h104) (by simpa [S₁] using h105)
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by simp; omega) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    simp [S₁, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
