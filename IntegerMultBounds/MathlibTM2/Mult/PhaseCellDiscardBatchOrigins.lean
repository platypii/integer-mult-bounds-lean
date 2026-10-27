module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchSetupHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWeightWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix

/-! Consume repeated origin packets without evaluating any weight coefficients. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def discardBatchOrigins : Pr P₀ 117 Q A U :=
  .seq generateRuntimeWidth (.seq generateWeightWidth
    (.seq (unaryProduct 116 115 64 104 105)
      (.seq (discardPrefix 64 109 65 104) (.seq (uclear 64) (clearWords [94,115])))))

def discardBatchOriginsCost (P q t u B : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  (4*q+5)+weightWidthCost P q w t u+(B*(4*V+9)+4)+(8*(B*V)+8)+(2*(w+V)+5)

theorem discardBatchOrigins_exec (P q t u B : ℕ) (lo : ℕ → ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hP : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (ht : (S.R 98).length = t) (hu : (S.R 99).length = u) (hB : (S.R 116).length = B)
    (hsource : S.R 109 = (List.range B).flatMap
      (fun i => binSyms (weightWorkspaceWidth P q (2*q+8) t u) (lo i))++tail)
    (hfresh : ∀ i ∈ ([(0 : Fin 117),1,2,3,4,64,65,94,104,105,115] : List (Fin 117)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ discardBatchOriginsCost P q t u B ∧
      Exec body discardBatchOrigins (mk v S) n
        (mk v' {S with R := Function.update S.R 109 tail}) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let packet : List (Fin (A+4)) := (List.range B).flatMap (fun i => binSyms V (lo i))
  have hlen : packet.length = B*V := by simp [packet,List.length_flatMap]
  obtain ⟨v₁,hu₁,he₁⟩ := generateRuntimeWidth_exec (body := body) q v S hq
    (hfresh 94 (by simp)) (hfresh 104 (by simp))
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 94 (List.replicate w tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generateWeightWidth_exec (body := body) P q w t u v₁ S₁
    (by simpa [S₁] using hP) (by simpa [S₁] using hq) (by simp [S₁])
    (by simpa [S₁] using ht) (by simpa [S₁] using hu) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [S₁] using hfresh _ (by simp))
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 115 (List.replicate V tick)}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := unaryProduct_exec (body := body)
    (show [(116 : Fin 117),115,64,104,105].Nodup by decide) v₂ S₂
    (by simp [S₂,S₁,hfresh 104 (by simp)]) (by simp [S₂,S₁,hfresh 105 (by simp)])
  let S₃ : Stacks 117 A := {S₂ with R := Function.update S₂.R 64 (List.replicate (B*V) tick)}
  have he₃' : Exec body (unaryProduct 116 115 64 104 105) (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,hB,hfresh 64 (by simp)] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := discardPrefix_exec (body := body)
    (show [(64 : Fin 117),109,65,104].Nodup by decide) packet tail v₃ S₃
    (by simpa [S₃,S₂,S₁,packet,V,w] using hsource) (by simp [S₃,hlen])
    (by simp [S₃,S₂,S₁,hfresh 65 (by simp)]) (by simp [S₃,S₂,S₁,hfresh 104 (by simp)])
  let S₄ : Stacks 117 A := {S₃ with R := Function.update S₃.R 109 tail}
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec (body := body) 64 v₄ S₄
  let S₅ : Stacks 117 A := {S₄ with R := Function.update S₄.R 64 []}
  obtain ⟨v₆,hu₆,he₆⟩ := clearWords_exec (body := body) [(94 : Fin 117),115] (by decide) v₅ S₅
  have hn₃' : n₃ ≤ B*(4*V+9)+4 := by simpa [S₂,S₁,hB] using hn₃
  refine ⟨v₆,(4*q+5)+(n₂+(n₃+((6*(B*V)+6)+((2*(B*V)+2)+(2*(w+V)+5))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,?_,⟩
  · dsimp only [discardBatchOriginsCost,V,w] at hn₂ hn₃' ⊢
    omega
  · refine (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast ?_ ?_
    · simp [S₅,S₄,S₃,S₂,S₁,hlen]
    · apply congrArg (mk v₆)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases h64 : i = 64 <;> by_cases h94 : i = 94 <;> by_cases h115 : i = 115 <;>
        simp [S₅,S₄,S₃,S₂,S₁,Function.update_apply,h64,h94,h115,
          hfresh 64 (by simp),hfresh 94 (by simp),hfresh 115 (by simp)]

/-- Repeated origin removal has linear packet cost and one width-construction bill. -/
theorem discardBatchOriginsCost_affine (P q t u B : ℕ) :
    discardBatchOriginsCost P q t u B = discardBatchOriginsCost P q t u 0+
      B*(12*weightWorkspaceWidth P q (2*q+8) t u+9) := by
  dsimp only [discardBatchOriginsCost]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
