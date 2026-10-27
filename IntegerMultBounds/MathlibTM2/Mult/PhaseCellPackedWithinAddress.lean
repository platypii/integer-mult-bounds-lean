module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClippedBandControls

/-! Add a selected row's displacement within its reversed clipped column block. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def packedWithinAddress : Pr P 154 Q A U :=
  .seq (bandIntervalEndpoints 107 94 137 138 135) (.seq (clipUnary 116 138 136 135)
    (.seq (.act (dropTop 138 .done)) (.seq (usub 108 138 135)
      (.seq (ucopy 138 0 135) (clearWords [137,138])))))

def packedWithinAddressCost (n m W N : ℕ) : ℕ :=
  let d := min N (n+W+1)-1-m
  bandIntervalEndpointsCost n W+(clipUnaryCost N (n+W+1)+(1+((4*m+4)+((4*d+4)+(2*((n-W)+d)+5)))))

theorem packedWithinAddress_exec (n m W N : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hn : (S.R 107).length = n) (hm : (S.R 108).length = m)
    (hW : (S.R 94).length = W) (hN : (S.R 116).length = N)
    (hfresh : ∀ k ∈ [(135 : Fin 154),136,137,138], S.R k = []) :
    ∃ v', v'.user = v.user ∧ Exec body packedWithinAddress (mk v S) (packedWithinAddressCost n m W N)
      (mk v' {S with R := Function.update S.R 0 (List.replicate (min N (n+W+1)-1-m) tick++S.R 0)}) := by
  let d := min N (n+W+1)-1-m
  obtain ⟨v₁,hu₁,he₁⟩ := bandIntervalEndpoints_exec (body := body)
    (index := 107) (band := 94) (cursor := 137) (count := 138) (tmp := 135) (by decide) n W v S hn hW (by
      intro k hk
      exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))
  let S₁ : Stacks 154 A := {S with R := Function.update (Function.update S.R
    137 (List.replicate (n-W) tick)) 138 (List.replicate (n+W+1) tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := clipUnary_exec (body := body) (total := 116) (count := 138) (saved := 136) (tmp := 135)
    (by decide) N (n+W+1) v₁ S₁ (by simpa [S₁] using hN) (by simp [S₁]) (by simp [S₁]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 138 (List.replicate (min N (n+W+1)) tick)}
  let S₃ : Stacks 154 A := {S₂ with R := Function.update S₂.R 138 (List.replicate (min N (n+W+1)-1) tick)}
  have he₃ : Exec body (.act (dropTop 138 .done)) (mk v₂ S₂) 1 (mk v₂ S₃) := by
    simpa [S₃,S₂,dropTop,Action.run,update_rt,List.tail_replicate] using Exec.act (body := body) (dropTop 138 .done) (mk v₂ S₂)
  obtain ⟨v₄,hu₄,he₄⟩ := usub_exec body (a := 108) (b := 138) (t := 135)
    (by decide) (by decide) (by decide) v₂ S₃ (by simpa [S₃,S₂,S₁] using hfresh 135 (by simp))
  let S₄ : Stacks 154 A := {S₃ with R := Function.update S₃.R 138 (List.replicate d tick)}
  have he₄' : Exec body (usub 108 138 135) (mk v₂ S₃) (4*m+4) (mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,S₁,hm,d,List.drop_replicate] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := ucopy_exec body (a := 138) (b := 0) (t := 135)
    (by decide) (by decide) (by decide) v₄ S₄ (by simpa [S₄,S₃,S₂,S₁] using hfresh 135 (by simp))
  let S₅ : Stacks 154 A := {S₄ with R := Function.update S₄.R 0 (List.replicate d tick++S.R 0)}
  have he₅' : Exec body (ucopy 138 0 135) (mk v₄ S₄) (4*d+4) (mk v₅ S₅) := by
    simpa [S₅,S₄,S₃,S₂,S₁] using he₅
  obtain ⟨v₆,hu₆,he₆⟩ := clearWords_exec (body := body) [(137 : Fin 154),138] (by decide) v₅ S₅
  have hsum : ([(137 : Fin 154),138].map (fun k => (S₅.R k).length)).sum = (n-W)+d := by simp [S₅,S₄,S₃,S₂,S₁]
  refine ⟨v₆,hu₆.trans (hu₅.trans (hu₄.trans (hu₂.trans hu₁))),
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄' (Exec.seq he₅' he₆))))).cast ?_ ?_⟩
  · rw [hsum]
    simp only [List.length_cons,List.length_nil]
    rfl
  · apply congrArg (mk v₆)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk0 : k = 0 <;> by_cases hk137 : k = 137 <;> by_cases hk138 : k = 138 <;>
      simp [S₅,S₄,S₃,S₂,S₁,d,hk0,hk137,hk138,hfresh 137 (by simp),hfresh 138 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
