module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherControl

/-! Read the owned batch-count packet saved beneath the construction factor page.
The arbitrary suffix, such as the FFT-length header, remains in its original slot. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def loadBatchHeader : Pr P₀ 117 Q A U := .seq (gatherRead 109 96 107) (uclear 107)

theorem loadBatchHeader_exec (B : ℕ) (tail : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsrc : S.R 109 = List.replicate B tick ++ blank :: tail)
    (h96 : S.R 96 = []) (h107 : S.R 107 = []) :
    ∃ v', v'.user = v.user ∧ Exec body loadBatchHeader (mk v S) (4 * B + 7)
      (mk v' { S with R := (Function.update (Function.update S.R 109 tail) 96 (List.replicate B tick)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := gatherRead_exec (body := body)
    (show [(109 : Fin 117), 96, 107].Nodup by decide) B tail v S hsrc
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update (Function.update S.R 109 tail)
    96 (List.replicate B tick)) 107 (blank :: List.replicate B tick)) }
  have he₁' : Exec body (gatherRead 109 96 107) (mk v S) (2 * B + 3) (mk v₁ S₁) := by
    simpa [S₁, h96, h107] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := uclear_exec body 107 v₁ S₁
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁' he₂).cast (by simp [S₁]; omega) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk : k = 107
    · subst k; simp [h107]
    simp [S₁, hk, Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
