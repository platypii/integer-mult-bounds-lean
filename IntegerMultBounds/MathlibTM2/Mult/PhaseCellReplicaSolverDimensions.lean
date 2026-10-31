module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplaceUnary

/-! Convert copied-page dimensions into the ordinary cached solver dimensions.
The generated cell count and temporary width are retired after use. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 121 Q A U}

def prepareReplicaSolverDimensions : Pr P 121 Q A U :=
  .seq (unaryProduct 116 115 64 104 105)
    (.seq (replaceUnary 102 103 105)
      (.seq (replaceUnary 64 116 105) (clearWords [64,115,94])))

def prepareReplicaSolverDimensionsCost (N B L w : ℕ) : ℕ :=
  10*(N*B)+11*N+2*(B*L)+4*L+2*B+2*w+23

theorem prepareReplicaSolverDimensions_exec (N B L w : ℕ) (v : HS 121 Q A U) (S : Stacks 121 A)
    (hN : (S.R 116).length = N) (hB : (S.R 115).length = B)
    (hL : (S.R 102).length = L) (hrows : (S.R 103).length = B*L) (hw : (S.R 94).length = w)
    (hfresh : ∀ k ∈ [(64 : Fin 121),104,105], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareReplicaSolverDimensionsCost N B L w ∧
      Exec body prepareReplicaSolverDimensions (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update
          (Function.update (Function.update S.R 103 (List.replicate L tick))
            116 (List.replicate (N*B) tick)) 64 []) 115 []) 94 [])}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [(116 : Fin 121),115,64,104,105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 121 A := {S with R := Function.update S.R 64 (List.replicate (N*B) tick)}
  have he₁' : Exec body (unaryProduct 116 115 64 104 105) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hN,hB,hfresh 64 (by simp),List.append_nil,S₁] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := replaceUnary_exec (body := body)
    (show [(102 : Fin 121),103,105].Nodup by decide) v₁ S₁ (by simp [S₁,hfresh 105 (by simp)])
  let S₂ : Stacks 121 A := {S₁ with R := Function.update S₁.R 103 (List.replicate L tick)}
  have he₂' : Exec body (replaceUnary 102 103 105) (mk v₁ S₁) (2*(B*L)+4*L+6) (mk v₂ S₂) := by
    simpa [S₂,S₁,hL,hrows] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := replaceUnary_exec (body := body)
    (show [(64 : Fin 121),116,105].Nodup by decide) v₂ S₂ (by simp [S₂,S₁,hfresh 105 (by simp)])
  let S₃ : Stacks 121 A := {S₂ with R := Function.update S₂.R 116 (List.replicate (N*B) tick)}
  have he₃' : Exec body (replaceUnary 64 116 105) (mk v₂ S₂) (2*N+4*(N*B)+6) (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,hN] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [(64 : Fin 121),115,94] (by decide) v₃ S₃
  have hclear : 2*([(64 : Fin 121),115,94].map (fun r => (S₃.R r).length)).sum+
      2*[(64 : Fin 121),115,94].length+1 = 2*(N*B)+2*B+2*w+7 := by
    simp [S₃,S₂,S₁,hB,hw]
    omega
  let F : Stacks 121 A := {S with R := (Function.update (Function.update (Function.update
    (Function.update (Function.update S.R 103 (List.replicate L tick))
      116 (List.replicate (N*B) tick)) 64 []) 115 []) 94 [])}
  have he₄' : Exec body (clearWords [64,115,94]) (mk v₃ S₃) (2*(N*B)+2*B+2*w+7) (mk v₄ F) := by
    rw [hclear] at he₄
    refine he₄.cast rfl ?_
    apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h64 : k = 64 <;> by_cases h115 : k = 115 <;> by_cases h94 : k = 94 <;>
      simp [S₃,S₂,S₁,F,Function.update_apply,h64,h115,h94]
  refine ⟨v₄,n₁+((2*(B*L)+4*L+6)+((2*N+4*(N*B)+6)+(2*(N*B)+2*B+2*w+7))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄'))⟩
  simp only [hN,hB] at hn₁
  dsimp only [prepareReplicaSolverDimensionsCost]
  nlinarith only [hn₁]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
