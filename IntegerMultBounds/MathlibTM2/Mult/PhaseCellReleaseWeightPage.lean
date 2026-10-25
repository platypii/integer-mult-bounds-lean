module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease

/-! Release both weight banks using only retained L/q headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def releaseWeightPage : Pr P₀ 117 Q A U :=
  .seq (umul 2 102 96 104) (.seq (umul 2 112 94 104)
    (.seq (.act (pushN 94 (fun _ => tick) 8 .done))
      (.seq (releaseFromDimensions 96 94 98 110 106 104 105)
        (.seq (uclear 96) (uclear 94)))))

def releaseWeightPageCost (L q : ℕ) : ℕ :=
  24 * L * (2 * q + 8) + 26 * L + 2 * (2 * q + 8) + 4 * q + 25

theorem releaseWeightPage_exec (L q : ℕ) (page tail : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hL : (S.R 102).length = L) (hq : (S.R 112).length = q)
    (hpage : page.length = 2 * L * (2 * q + 8)) (hsrc : S.R 110 = page ++ tail)
    (hfresh : ∀ k ∈ [(94 : Fin 117), 96, 98, 104, 105, 106], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseWeightPageCost L q ∧
      Exec body releaseWeightPage (mk v S) m
        (mk v' { S with R := Function.update S.R 110 tail }) := by
  let w := 2 * q + 8
  obtain ⟨v₁, hu₁, he₁⟩ := umul_exec (body := body) 2 (a := 102) (b := 96) (t := 104)
    (by decide) (by decide) (by decide) v S (hfresh 104 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 96 (List.replicate (2 * L) tick) }
  have he₁' : Exec body (umul 2 102 96 104) (mk v S) (4 * L + 4) (mk v₁ S₁) := by
    simpa [S₁, hL, hfresh 96 (by simp)] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := umul_exec (body := body) 2 (a := 112) (b := 94) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 104 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 94 (List.replicate (2 * q) tick) }
  have he₂' : Exec body (umul 2 112 94 104) (mk v₁ S₁) (4 * q + 4) (mk v₂ S₂) := by
    simpa [S₂, S₁, hq, hfresh 94 (by simp)] using he₂
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 94 (List.replicate w tick) }
  have he₃ : Exec body (.act (pushN 94 (fun _ => tick) 8 .done)) (mk v₂ S₂) 1 (mk v₂ S₃) := by
    have he := Exec.act (body := body) (pushN 94 (fun _ => tick) 8 .done) (mk v₂ S₂)
    rw [pushN_run] at he
    simpa only [S₃, S₂, Action.run, Function.update_self, List.replicate_append_replicate,
      show 8 + 2 * q = w by dsimp [w]; omega] using he
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := releaseFromDimensions_exec (body := body)
    (show [(96 : Fin 117), 94, 98, 110, 106, 104, 105].Nodup by decide) v₂ S₃ page tail
    (by simpa [S₃, S₂, S₁] using hsrc) (by simpa [S₃, S₂, S₁, w] using hpage)
    (by simpa [S₃, S₂, S₁] using hfresh 98 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 106 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 110 tail }
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body 96 v₄ S₄
  let S₅ : Stacks 117 A := { S₄ with R := Function.update S₄.R 96 [] }
  obtain ⟨v₆, hu₆, he₆⟩ := uclear_exec body 94 v₅ S₅
  have h96 : (S₄.R 96).length = 2 * L := by simp [S₄, S₃, S₂, S₁]
  have h94 : (S₅.R 94).length = w := by simp [S₅, S₄, S₃]
  refine ⟨v₆, (4 * L + 4) + ((4 * q + 4) + (1 + (m₄ + ((2 * (2 * L) + 2) + (2 * w + 2))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₂.trans hu₁))), ?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast
      (by rw [h96, h94]) ?_⟩
  · simp only [S₃, S₂, S₁, Function.update_of_ne (by decide : (96 : Fin 117) ≠ 94),
      Function.update_self, List.length_replicate, hpage] at hm₄
    unfold releaseWeightPageCost
    dsimp only [w] at *
    nlinarith only [hm₄]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk94 : k = 94
      · subst k; simp [S₅, S₄, S₃, S₂, S₁, hfresh 94 (by simp)]
      by_cases hk96 : k = 96
      · subst k; simp [S₅, S₄, S₃, S₂, S₁, hfresh 96 (by simp)]
      simp [S₅, S₄, S₃, S₂, S₁, Function.update_apply, hk94, hk96]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
