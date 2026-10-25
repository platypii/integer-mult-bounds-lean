module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeedExec

/-! # Generate the reciprocal numerator from retained precision headers -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateReciprocalNumerator : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 114 116 107 104 105)
    (.seq (uadd 112 107 104)
      (.seq (.act (pushN 97 (fun _ => tick) 1 .done))
        (.seq (generateSeed 97 94 107 96 99 104 105 106) (clearWords [97, 107]))))

theorem generateReciprocalNumerator_exec (P n q W : ℕ) (hn : 1 ≤ n) (hd : q + P * n < W)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hnR : (S.R 116).length = n)
    (hq : (S.R 112).length = q) (hW : (S.R 94).length = W)
    (hfresh : ∀ k ∈ [(97 : Fin 117), 99, 104, 105, 106, 107], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 31 * W + 42 ∧
      Exec body generateReciprocalNumerator (mk v S) m
        (mk v' { S with R := (Function.update S.R 96
          (csyms A W (⟨(2 : ℤ) ^ (q + P * n), 0⟩ : GaussianInt) ++ S.R 96)) }) := by
  let d := q + P * n
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(114 : Fin 117), 116, 107, 104, 105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 107 (List.replicate (P * n) tick) }
  have he₁' : Exec body (unaryProduct 114 116 107 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁, hP, hnR, hfresh 107 (by simp)] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := uadd_exec (body := body) (a := 112) (b := 107) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 104 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 107 (List.replicate d tick) }
  have he₂' : Exec body (uadd 112 107 104) (mk v₁ S₁) (4 * q + 4) (mk v₂ S₂) := by
    simpa [S₂, S₁, hq, List.replicate_append_replicate, d] using he₂
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 97 [tick] }
  have he₃ : Exec body (.act (pushN 97 (fun _ => tick) 1 .done)) (mk v₂ S₂) 1 (mk v₂ S₃) := by
    have he := Exec.act (body := body) (pushN 97 (fun _ => tick) 1 .done) (mk v₂ S₂)
    rw [pushN_run] at he
    simpa [Action.run, S₃, S₂, S₁, hfresh 97 (by simp)] using he
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := generateSeed_exec (body := body)
    (show [(97 : Fin 117), 94, 107, 96, 99, 104, 105, 106].Nodup by decide)
    1 W d (by decide) hd v₂ S₃ (by simp [S₃]) (by simpa [S₃, S₂, S₁] using hW)
    (by simp [S₃, S₂]) (by simpa [S₃, S₂, S₁] using hfresh 99 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 105 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 106 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 96 (cstream A W (seedWords d 1) ++ S₃.R 96) }
  obtain ⟨v₅, hu₅, he₅⟩ := clearWords_exec (body := body) [97, 107] (by decide) v₄ S₄
  have hsum : ([(97 : Fin 117), 107].map (fun k => (S₄.R k).length)).sum = 1 + d := by
    simp [S₄, S₃, S₂]
  have hP' : P ≤ P * n := by nlinarith
  rw [hP, hnR] at hm₁
  refine ⟨v₅, m₁ + ((4 * q + 4) + (1 + (m₄ + (2 * (1 + d) + 5)))),
    hu₅.trans (hu₄.trans (hu₂.trans hu₁)), ?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp [d] at hm₄ ⊢
    nlinarith only [hm₁, hm₄, hP', hd]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ho : k = 96
    · subst k; simp [S₄, S₃, S₂, S₁, seedWords, cstream, d]
    by_cases h97 : k = 97
    · subst k; simp [hfresh 97 (by simp)]
    by_cases h107 : k = 107
    · subst k; simp [hfresh 107 (by simp)]
    simp [S₄, S₃, S₂, S₁, ho, h97, h107]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
