module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Copy both halves of one retained weight page across an equal-key batch.
The original page and every borrowed suffix survive this staging operation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def repeatWeightBanks : Pr P₀ 117 Q A U :=
  .seq (transfer 64 110 107 105) (.seq (repeatPrefix 116 108 64 110 113 104 105)
    (.seq (moveR 107 110 id) (repeatPrefix 116 108 64 110 95 104 105)))

theorem repeatWeightBanks_exec (B r : ℕ) (xs ys tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hB : (S.R 116).length = B) (hr : (S.R 64).length = r)
    (hxs : xs.length = r) (hys : ys.length = r) (hsrc : S.R 110 = xs++(ys++tail))
    (hfresh : ∀ k ∈ [(104 : Fin 117),105,107,108], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ B*(20*r+30)+6*r+14 ∧
      Exec body repeatWeightBanks (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R
          95 ((List.replicate B xs).flatten++S.R 95))
          113 ((List.replicate B ys).flatten++S.R 113)) }) := by
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body)
    (show [(64 : Fin 117),110,107,105].Nodup by decide) v S xs (ys++tail) hsrc
    (hr.trans hxs.symm) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update S.R
    110 (ys++tail)) 107 xs.reverse) }
  have he₁' : Exec body (transfer 64 110 107 105) (mk v S) (4*r+4) (mk v₁ S₁) := by
    simpa [S₁,hxs,hfresh 107 (by simp)] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := repeatPrefix_exec (body := body)
    (show [(116 : Fin 117),108,64,110,113,104,105].Nodup by decide) B ys tail v₁ S₁
    (by simpa [S₁] using hB) (by simpa [S₁,hys] using hr) (by simp [S₁]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 113 ((List.replicate B ys).flatten++S.R 113) }
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body 107 110 (by decide) id v₂ S₂
  let S₃ : Stacks 117 A := { S₂ with R := (Function.update (Function.update S₂.R
    107 []) 110 (xs++(ys++tail))) }
  have he₃' : Exec body (moveR 107 110 id) (mk v₂ S₂) (2*r+2) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,movedR,hxs] using he₃
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := repeatPrefix_exec (body := body)
    (show [(116 : Fin 117),108,64,110,95,104,105].Nodup by decide) B xs (ys++tail) v₃ S₃
    (by simpa [S₃,S₂,S₁] using hB) (by simpa [S₃,S₂,S₁,hxs] using hr) (by simp [S₃]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simpa [S₃,S₂,S₁] using hfresh _ (by simp))
  refine ⟨v₄,(4*r+4)+(n₂+((2*r+2)+n₄)),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' he₄))).cast rfl ?_⟩
  · rw [hys] at hn₂
    rw [hxs] at hn₄
    nlinarith only [hn₂,hn₄]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h107 : k = 107
    · subst k; simp [S₃,S₂,S₁,hfresh 107 (by simp)]
    by_cases h110 : k = 110
    · subst k; simp [S₃,S₂,S₁,hsrc]
    by_cases h95 : k = 95 <;> by_cases h113 : k = 113 <;>
      simp [S₃,S₂,S₁,h107,h110,h95,h113]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
