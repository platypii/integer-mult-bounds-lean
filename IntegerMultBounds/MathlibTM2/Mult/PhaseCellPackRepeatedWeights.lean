module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackWeightBatch

/-! Release the single generated source page and publish its repeated banks.
The row counter is owned; staged-bank suffixes and all scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def packRepeatedWeights : Pr P₀ 117 Q A U :=
  .seq (releasePrefix 64 110 104 105) (.seq (releasePrefix 64 110 104 105)
    (.seq packWeightBatch (uclear 64)))

theorem packRepeatedWeights_exec (B r : ℕ) (xs ys tail tailX tailY : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hB : (S.R 116).length = B) (hr : (S.R 64).length = r)
    (hxs : xs.length = r) (hys : ys.length = r) (hsrc : S.R 110 = xs++(ys++tail))
    (hx : S.R 95 = (List.replicate B xs).flatten++tailX)
    (hy : S.R 113 = (List.replicate B ys).flatten++tailY)
    (hfresh : ∀ k ∈ [(65 : Fin 117),104,105,106,108], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ B*(50*r+47)+14*r+44 ∧
      Exec body packRepeatedWeights (mk v S) n
        (mk v' { S with R := (Function.update (Function.update (Function.update (Function.update S.R
          64 []) 95 tailX) 113 tailY) 110
          ((List.replicate B xs).flatten++((List.replicate B ys).flatten++tail))) }) := by
  obtain ⟨v₁,hu₁,he₁⟩ := releasePrefix_exec (body := body)
    (show [(64 : Fin 117),110,104,105].Nodup by decide) v S xs (ys++tail)
    hsrc (hr.trans hxs.symm) (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 110 (ys++tail) }
  obtain ⟨v₂,hu₂,he₂⟩ := releasePrefix_exec (body := body)
    (show [(64 : Fin 117),110,104,105].Nodup by decide) v₁ S₁ ys tail
    (by simp [S₁]) (by simpa [S₁,hys] using hr)
    (by simpa [S₁] using hfresh 104 (by simp)) (by simpa [S₁] using hfresh 105 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 110 tail }
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := packWeightBatch_exec (body := body) r B
    (List.replicate B xs) (List.replicate B ys) (by simp) (by simp)
    (by intro z hz; simpa only [(List.mem_replicate.mp hz).2] using hxs)
    (by intro z hz; simpa only [(List.mem_replicate.mp hz).2] using hys)
    v₂ S₂ tailX tailY (by simpa [S₂,S₁] using hr) (by simpa [S₂,S₁] using hB)
    (by simpa [S₂,S₁] using hx) (by simpa [S₂,S₁] using hy) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simpa [S₂,S₁] using hfresh _ (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := (Function.update (Function.update (Function.update S₂.R
    110 ((List.replicate B xs).flatten++(List.replicate B ys).flatten++tail)) 95 tailX) 113 tailY) }
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec body 64 v₃ S₃
  refine ⟨v₄,6*xs.length+6+((6*ys.length+6)+(n₃+(2*r+2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · dsimp only [packWeightBatchCost] at hn₃
    rw [hxs,hys]
    omega
  · simp [S₃,S₂,S₁,hr]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h64 : k = 64
    · subst k; simp [S₃,S₂,S₁]
    by_cases h110 : k = 110
    · subst k; simp [S₃,S₂,S₁,List.append_assoc]
    simp [S₃,S₂,S₁,Function.update_apply,h64,h110]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
