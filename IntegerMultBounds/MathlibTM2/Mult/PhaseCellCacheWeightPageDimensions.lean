module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCacheWeightPage
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Install a weight page and its replay clock from ordinary unary dimensions,
then retire the generated counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 121 Q A U}

def cacheWeightPageFromDimensions : Pr P 121 Q A U :=
  .seq (unaryProduct 116 103 65 104 105)
    (.seq (unaryProduct 65 94 64 104 105)
      (.seq cacheWeightPage (clearWords [64,65])))

def cacheWeightPageFromDimensionsCost (N rows w : ℕ) : ℕ :=
  26*(N*rows*w)+15*(N*rows)+9*N+27

theorem cacheWeightPageFromDimensions_exec (N rows w : ℕ)
    (page tail : List (Fin (A+4))) (hlen : page.length = 2*(N*rows*w))
    (v : HS 121 Q A U) (S : Stacks 121 A)
    (hN : (S.R 116).length = N) (hrows : (S.R 103).length = rows) (hw : (S.R 94).length = w)
    (hsource : S.R 110 = page++tail)
    (hfresh : ∀ k ∈ [(64 : Fin 121),65,104,105,118,119,120], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cacheWeightPageFromDimensionsCost N rows w ∧
      Exec body cacheWeightPageFromDimensions (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 110 tail)
          117 (page++S.R 117)) 118 (List.replicate (2*(N*rows*w)) tick))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [(116 : Fin 121),103,65,104,105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 121 A := {S with R := Function.update S.R 65 (List.replicate (N*rows) tick)}
  have he₁' : Exec body (unaryProduct 116 103 65 104 105) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hN,hrows,hfresh 65 (by simp),List.append_nil,S₁] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body)
    (show [(65 : Fin 121),94,64,104,105].Nodup by decide) v₁ S₁
    (by simp [S₁,hfresh 104 (by simp)]) (by simp [S₁,hfresh 105 (by simp)])
  let S₂ : Stacks 121 A := {S₁ with R := Function.update S₁.R 64 (List.replicate (N*rows*w) tick)}
  have he₂' : Exec body (unaryProduct 65 94 64 104 105) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₁,S₂,hw,hfresh 64 (by simp)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := cacheWeightPage_exec (body := body) v₂ S₂ page tail (N*rows*w)
    hlen (by simpa [S₂,S₁] using hsource) (by simp [S₂])
    (by simp [S₂,S₁,hfresh 118 (by simp)])
    (by simp [S₂,S₁,hfresh 119 (by simp)])
    (by simp [S₂,S₁,hfresh 120 (by simp)])
  let S₃ : Stacks 121 A := {S₂ with R := (Function.update (Function.update (Function.update S₂.R 110 tail)
    117 (page++S₂.R 117)) 118 (List.replicate (2*(N*rows*w)) tick))}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [(64 : Fin 121),65] (by decide) v₃ S₃
  have hclear : 2*([(64 : Fin 121),65].map (fun r => (S₃.R r).length)).sum+
      2*[(64 : Fin 121),65].length+1 = 2*(N*rows*w)+2*(N*rows)+5 := by
    simp [S₃,S₂,S₁]
    omega
  let F : Stacks 121 A := {S with R := (Function.update (Function.update (Function.update S.R 110 tail)
    117 (page++S.R 117)) 118 (List.replicate (2*(N*rows*w)) tick))}
  have he₄' : Exec body (clearWords [64,65]) (mk v₃ S₃)
      (2*(N*rows*w)+2*(N*rows)+5) (mk v₄ F) := by
    rw [hclear] at he₄
    refine he₄.cast rfl ?_
    apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h64 : k = 64
    · subst k; simp [F,hfresh 64 (by simp)]
    by_cases h65 : k = 65
    · subst k; simp [F,hfresh 65 (by simp)]
    simp [S₃,S₂,S₁,F,Function.update_apply,h64,h65]
  refine ⟨v₄,n₁+(n₂+((20*(N*rows*w)+14)+(2*(N*rows*w)+2*(N*rows)+5))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄'))⟩
  simp only [hN,hrows] at hn₁
  have hn₂' : n₂ ≤ (N*rows)*(4*w+9)+4 := by simpa [S₁,hw] using hn₂
  dsimp only [cacheWeightPageFromDimensionsCost]
  nlinarith only [hn₁,hn₂']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
