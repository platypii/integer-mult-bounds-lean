module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease

/-! # Paid release of a packed runtime generator page -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def releaseGeneratorPage : Pr P₀ 117 Q A U :=
  .seq (umul 2 112 98 104)
    (.seq (.act (pushN 98 (fun _ => tick) 8 .done))
      (.seq (unaryProduct 102 98 99 104 105)
        (.seq (umul 2 99 97 104)
          (.seq (uadd 98 97 104)
            (.seq (releasePrefix 97 110 104 105) (clearWords [97, 98, 99]))))))

def releaseGeneratorPageCost (L q : ℕ) : ℕ :=
  26 * (L * (2 * q + 8)) + 14 * (2 * q + 8) + 9 * L + 4 * q + 30

/-- The entire generator page is released without inspecting the borrowed suffix.
All counter symbols and every stack except the released prefix restore. -/
theorem releaseGeneratorPage_exec (L q : ℕ) (pre tail : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hrows : (S.R 102).length = L) (hq : (S.R 112).length = q)
    (hpre : pre.length = (2 * L + 1) * (2 * q + 8)) (hsrc : S.R 110 = pre ++ tail)
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseGeneratorPageCost L q ∧
      Exec body releaseGeneratorPage (mk v S) m (mk v' { S with R := Function.update S.R 110 tail }) := by
  let w := 2 * q + 8
  obtain ⟨v₁, hu₁, he₁⟩ := umul_exec (body := body) 2 (a := 112) (b := 98) (t := 104)
    (by decide) (by decide) (by decide) v S (hfresh 104 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 98 (List.replicate (2 * q) tick) }
  have he₁' : Exec body (umul 2 112 98 104) (mk v S) (4 * q + 4) (mk v₁ S₁) := by
    simpa [S₁, hq, hfresh 98 (by simp)] using he₁
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 98 (List.replicate w tick) }
  have he₂ : Exec body (.act (pushN 98 (fun _ => tick) 8 .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    have he := Exec.act (body := body) (pushN 98 (fun _ => tick) 8 .done) (mk v₁ S₁)
    rw [pushN_run] at he
    simpa only [S₂, S₁, Action.run, Function.update_self, List.replicate_append_replicate,
      show 8 + 2 * q = w by dsimp [w]; omega] using he
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := unaryProduct_exec (body := body)
    (show [(102 : Fin 117), 98, 99, 104, 105].Nodup by decide) v₁ S₂
    (by simpa [S₂, S₁] using hfresh 104 (by simp)) (by simpa [S₂, S₁] using hfresh 105 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 99 (List.replicate (L * w) tick) }
  have he₃' : Exec body (unaryProduct 102 98 99 104 105) (mk v₁ S₂) m₃ (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁, hrows, hfresh 99 (by simp)] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := umul_exec (body := body) 2 (a := 99) (b := 97) (t := 104)
    (by decide) (by decide) (by decide) v₃ S₃ (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 97 (List.replicate (2 * (L * w)) tick) }
  have he₄' : Exec body (umul 2 99 97 104) (mk v₃ S₃) (4 * (L * w) + 4) (mk v₄ S₄) := by
    simpa [S₄, S₃, S₂, S₁, hfresh 97 (by simp)] using he₄
  obtain ⟨v₅, hu₅, he₅⟩ := uadd_exec (body := body) (a := 98) (b := 97) (t := 104)
    (by decide) (by decide) (by decide) v₄ S₄ (by simpa [S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
  let S₅ : Stacks 117 A := { S₄ with R := Function.update S₄.R 97 (List.replicate ((2 * L + 1) * w) tick) }
  have he₅' : Exec body (uadd 98 97 104) (mk v₄ S₄) (4 * w + 4) (mk v₅ S₅) := by
    have hlen : w + 2 * (L * w) = (2 * L + 1) * w := by ring
    simpa [S₅, S₄, S₃, S₂, List.replicate_append_replicate, hlen] using he₅
  obtain ⟨v₆, hu₆, he₆⟩ := releasePrefix_exec (body := body)
    (show [(97 : Fin 117), 110, 104, 105].Nodup by decide) v₅ S₅ pre tail
    (by simpa [S₅, S₄, S₃, S₂, S₁] using hsrc) (by simp [S₅, hpre, w])
    (by simpa [S₅, S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₅, S₄, S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₆ : Stacks 117 A := { S₅ with R := Function.update S₅.R 110 tail }
  obtain ⟨v₇, hu₇, he₇⟩ := clearWords_exec (body := body) [97, 98, 99] (by decide) v₆ S₆
  have hsum : ([(97 : Fin 117), 98, 99].map (fun k => (S₆.R k).length)).sum = (3 * L + 2) * w := by
    simp [S₆, S₅, S₄, S₃, S₂]; ring
  have hrows₂ : (S₂.R 102).length = L := by simp [S₂, S₁, hrows]
  have hw₂ : (S₂.R 98).length = w := by simp [S₂]
  rw [hrows₂, hw₂] at hm₃
  refine ⟨v₇, (4 * q + 4) + (1 + (m₃ + ((4 * (L * w) + 4) + ((4 * w + 4) +
    ((6 * ((2 * L + 1) * w) + 6) + (2 * ((3 * L + 2) * w) + 7)))))),
    hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans hu₁)))), ?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅' (Exec.seq he₆ he₇)))))).cast ?_ ?_⟩
  · unfold releaseGeneratorPageCost
    dsimp [w] at hm₃ ⊢
    nlinarith only [hm₃]
  · rw [hsum, hpre]; rfl
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h97 : k = 97
    · subst k; simp [hfresh 97 (by simp)]
    by_cases h98 : k = 98
    · subst k; simp [hfresh 98 (by simp)]
    by_cases h99 : k = 99
    · subst k; simp [hfresh 99 (by simp)]
    simp [S₆, S₅, S₄, S₃, S₂, S₁, h97, h98, h99, Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
