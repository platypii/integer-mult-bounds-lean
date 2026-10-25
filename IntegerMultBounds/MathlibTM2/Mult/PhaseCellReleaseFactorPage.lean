module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease

/-! # Release an owned square factor page with generated counts -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def releaseFactorPage : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 102 103 99 104 105)
    (.seq (releaseFromDimensions 99 94 97 109 104 105 106) (uclear 99))

def releaseFactorPageCost (L W : ℕ) : ℕ := 12 * (L * L * W) + 15 * (L * L) + 9 * L + 18

theorem releaseFactorPage_exec (L W : ℕ) (pre tail : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L) (hwidth : (S.R 94).length = W)
    (hpre : pre.length = L * L * W) (hsrc : S.R 109 = pre ++ tail)
    (hfresh : ∀ k ∈ [(97 : Fin 117), 99, 104, 105, 106], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseFactorPageCost L W ∧
      Exec body releaseFactorPage (mk v S) m (mk v' { S with R := Function.update S.R 109 tail }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(102 : Fin 117), 103, 99, 104, 105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 99 (List.replicate (L * L) tick) }
  have he₁' : Exec body (unaryProduct 102 103 99 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁, hrows, hcount, hfresh 99 (by simp)] using he₁
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseFromDimensions_exec (body := body)
    (show [(99 : Fin 117), 94, 97, 109, 104, 105, 106].Nodup by decide) v₁ S₁ pre tail
    (by simpa [S₁] using hsrc) (by simp [S₁, hpre, hwidth])
    (by simpa [S₁] using hfresh 97 (by simp)) (by simpa [S₁] using hfresh 104 (by simp))
    (by simpa [S₁] using hfresh 105 (by simp)) (by simpa [S₁] using hfresh 106 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 109 tail }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 99 v₂ S₂
  have hlen : (S₂.R 99).length = L * L := by simp [S₂, S₁]
  rw [hrows, hcount] at hm₁
  have hm₂' : m₂ ≤ 12 * (L * L * W) + 9 * (L * L) + 12 := by simpa [hpre, S₁] using hm₂
  refine ⟨v₃, m₁ + (m₂ + (2 * (L * L) + 2)), hu₃.trans (hu₂.trans hu₁),
    by unfold releaseFactorPageCost; nlinarith only [hm₁, hm₂'],
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hlen]) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hk : k = 99
  · subst k; simp [hfresh 99 (by simp)]
  simp [S₂, S₁, hk, Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
