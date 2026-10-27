module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCacheWeightPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightPage

/-! Build a grouped weight-cache clock from the actual batch/row/word headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

def cacheBatchWeightPage : Pr P₀ 121 Q A U :=
  .seq (unaryProduct 103 94 65 104 105)
    (.seq (unaryProduct 116 65 64 104 105)
      (.seq (uclear 65) (.seq cacheWeightPage (uclear 64))))

def cacheBatchWeightPageCost (B L w : ℕ) : ℕ :=
  L*(4*w+9)+B*(4*(L*w)+9)+2*(L*w)+22*(B*(L*w))+26

theorem cacheBatchWeightPage_exec (v : HS 121 Q A U) (S : Stacks 121 A)
    (page tail : List (Fin (A+4))) (B L w : ℕ) (hlen : page.length = 2*(B*(L*w)))
    (hsource : S.R 110 = page++tail) (hB : (S.R 116).length = B)
    (hL : (S.R 103).length = L) (hw : (S.R 94).length = w)
    (hfresh : ∀ i ∈ ([(64 : Fin 121),65,104,105,118,119,120] : List (Fin 121)), S.R i = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ cacheBatchWeightPageCost B L w ∧
      Exec body cacheBatchWeightPage (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 110 tail)
          117 (page++S.R 117)) 118 (List.replicate (2*(B*(L*w))) tick))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [(103 : Fin 121),94,65,104,105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 121 A := {S with R := Function.update S.R 65 (List.replicate (L*w) tick)}
  have he₁' : Exec body (unaryProduct 103 94 65 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,hL,hw,hfresh 65 (by simp)] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := unaryProduct_exec (body := body)
    (show [(116 : Fin 121),65,64,104,105].Nodup by decide) v₁ S₁
    (by simp [S₁,hfresh 104 (by simp)]) (by simp [S₁,hfresh 105 (by simp)])
  let S₂ : Stacks 121 A := {S₁ with R := Function.update S₁.R 64 (List.replicate (B*(L*w)) tick)}
  have he₂' : Exec body (unaryProduct 116 65 64 104 105) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,hB,hfresh 64 (by simp)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 65 v₂ S₂
  let S₃ : Stacks 121 A := {S₂ with R := Function.update S₂.R 65 []}
  obtain ⟨v₄,hu₄,he₄⟩ := cacheWeightPage_exec (body := body) v₃ S₃ page tail (B*(L*w)) hlen
    (by simpa [S₃,S₂,S₁] using hsource) (by simp [S₃,S₂])
    (by simp [S₃,S₂,S₁,hfresh 118 (by simp)])
    (by simp [S₃,S₂,S₁,hfresh 119 (by simp)])
    (by simp [S₃,S₂,S₁,hfresh 120 (by simp)])
  let S₄ : Stacks 121 A := {S₃ with R := (Function.update (Function.update (Function.update S₃.R 110 tail)
    117 (page++S₃.R 117)) 118 (List.replicate (2*(B*(L*w))) tick))}
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec (body := body) 64 v₄ S₄
  refine ⟨v₅,m₁+(m₂+(2*(L*w)+2+((20*(B*(L*w))+14)+(2*(B*(L*w))+2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,?_,⟩
  · dsimp only [cacheBatchWeightPageCost]
    simp only [hL,hw] at hm₁
    simp [S₁,hB] at hm₂
    omega
  · have e := Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))
    refine e.cast ?_ ?_
    · simp [S₄,S₃,S₂,S₁]
    · apply congrArg (mk v₅)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases h64 : i = 64 <;> by_cases h65 : i = 65 <;>
        simp [S₄,S₃,S₂,S₁,Function.update_apply,h64,h65,hfresh 64 (by simp),hfresh 65 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
