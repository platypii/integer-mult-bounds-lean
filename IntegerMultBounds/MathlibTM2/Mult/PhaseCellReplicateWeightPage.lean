module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatWeightBanks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackRepeatedWeights

/-! Expand one exact output/input weight page for equal-key replicas.
Only counted copying is repeated; numerical weight evaluation is absent. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def replicateWeightPage : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 103 94 64 104 105) (.seq repeatWeightBanks packRepeatedWeights)

def replicateWeightPageCost (B L w : ℕ) : ℕ :=
  B*(70*(L*w)+77)+24*(L*w)+9*L+62

theorem replicateWeightPage_exec (B L w : ℕ) (xs ys tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hB : (S.R 116).length = B) (hL : (S.R 103).length = L) (hw : (S.R 94).length = w)
    (hxs : xs.length = L*w) (hys : ys.length = L*w) (hsrc : S.R 110 = xs++(ys++tail))
    (hfresh : ∀ k ∈ [(64 : Fin 117),65,104,105,106,107,108], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ replicateWeightPageCost B L w ∧
      Exec body replicateWeightPage (mk v S) n
        (mk v' { S with R := (Function.update S.R 110
          ((List.replicate B xs).flatten++((List.replicate B ys).flatten++tail))) }) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [(103 : Fin 117),94,64,104,105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 64 (List.replicate (L*w) tick) }
  have he₁' : Exec body (unaryProduct 103 94 64 104 105) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hL,hw,hfresh 64 (by simp)] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := repeatWeightBanks_exec (body := body) B (L*w) xs ys tail v₁ S₁
    (by simpa [S₁] using hB) (by simp [S₁]) hxs hys (by simpa [S₁] using hsrc) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update (Function.update S₁.R
    95 ((List.replicate B xs).flatten++S.R 95)) 113 ((List.replicate B ys).flatten++S.R 113)) }
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := packRepeatedWeights_exec (body := body) B (L*w)
    xs ys tail (S.R 95) (S.R 113) v₂ S₂
    (by simpa [S₂,S₁] using hB) (by simp [S₂,S₁]) hxs hys
    (by simpa [S₂,S₁] using hsrc) (by simp [S₂]) (by simp [S₂]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simpa [S₂,S₁] using hfresh _ (by simp))
  refine ⟨v₃,n₁+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · simp only [hL,hw] at hn₁
    dsimp only [replicateWeightPageCost]
    nlinarith only [hn₁,hn₂,hn₃]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h64 : k = 64
    · subst k; simp [S₂,S₁,hfresh 64 (by simp)]
    by_cases h95 : k = 95
    · subst k; simp [S₂,S₁]
    by_cases h113 : k = 113
    · subst k; simp [S₂,S₁]
    simp [S₂,S₁,Function.update_apply,h64,h95,h113]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
