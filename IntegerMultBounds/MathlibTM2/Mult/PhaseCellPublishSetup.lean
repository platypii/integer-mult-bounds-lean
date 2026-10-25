module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHalfCount

/-! # Publication from ordinary retained cell dimensions -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def publishFromDimensions : Pr P 117 Q A U :=
  .seq (halfCount 108 4 1)
    (.seq (unaryProduct 103 94 2 7 8)
      (.seq (publishRows 1 4 103 5 94 2 93 6 9 10 11 7 8 84 3) (clearWords [1, 2])))

def publishFromDimensionsCost (M L w : ℕ) : ℕ :=
  42 * (M * L * w) + 19 * (M * L) + 34 * M + 6 * (L * w) + 9 * L + 37

theorem publishFromDimensions_exec (M L w : ℕ) (blocks : List (List GaussianInt))
    (hblocks : blocks.length = M) (hlen : ∀ xs ∈ blocks, xs.length = L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R 108).length = 2 * M) (hrows : (S.R 103).length = L) (hwidth : (S.R 94).length = w)
    (hsrc : S.R 93 = cstream A w blocks.flatten ++ tail)
    (hclean : ∀ k ∈ [(1 : Fin 117), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 84], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ publishFromDimensionsCost M L w ∧
      Exec body publishFromDimensions (mk v S) m
        (mk v' { S with R := Function.update S.R 93 (cstream A w (blocks.flatMap List.reverse) ++ tail) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := halfCount_exec (body := body)
    (count := 108) (saved := 4) (dst := 1) (by decide) M v S hbatch (hclean 4 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 1 (List.replicate M tick) }
  have he₁' : Exec body (halfCount 108 4 1) (mk v S) (6 * M + 4) (mk v₁ S₁) := by
    simpa only [hclean 1 (by simp), List.append_nil] using he₁
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := unaryProduct_exec (body := body)
    (a := 103) (b := 94) (dst := 2) (t₁ := 7) (t₂ := 8) (by decide) v₁ S₁
    (by simp [S₁, hclean 7 (by simp)]) (by simp [S₁, hclean 8 (by simp)])
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 2 (List.replicate (L * w) tick) }
  have he₂' : Exec body (unaryProduct 103 94 2 7 8) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₁, Function.update_of_ne (by decide : (103 : Fin 117) ≠ 1),
      Function.update_of_ne (by decide : (94 : Fin 117) ≠ 1), hrows, hwidth,
      Function.update_of_ne (by decide : (2 : Fin 117) ≠ 1), hclean 2 (by simp), List.append_nil] using he₂
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := publishRows_exec (body := body)
    (dst := 84) (batch := 1) (batchSaved := 4) (rows := 103) (recordSaved := 5) (width := 94)
    (recordSymbols := 2) (src := 93) (acc := 6) (current := 9) (savedSource := 10) (saved := 11)
    (buf := 7) (tmp := 8) (count := 3) (by decide) w L blocks hlen v₂ S₂ tail
    (by simp [S₂, S₁, hblocks]) (by simpa [S₂, S₁] using hsrc)
    (by simpa [S₂, S₁] using hrows) (by simpa [S₂, S₁] using hwidth) (by simp [S₂])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp [S₂, S₁];
          exact hclean _ (by simp)))
  let result := cstream A w (blocks.flatMap List.reverse) ++ tail
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 93 result }
  obtain ⟨v₄, hu₄, he₄⟩ := clearWords_exec (body := body) [1, 2] (by decide) v₃ S₃
  have hclear : 2 * (([1, 2] : List (Fin 117)).map (fun k => (S₃.R k).length)).sum +
      2 * ([1, 2] : List (Fin 117)).length + 1 = 2 * (M + L * w) + 5 := by simp [S₃, S₂, S₁]
  refine ⟨v₄, (6 * M + 4) + (m₂ + (m₃ + (2 * (M + L * w) + 5))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_⟩
  · simp only [S₁, Function.update_of_ne (by decide : (103 : Fin 117) ≠ 1),
      Function.update_of_ne (by decide : (94 : Fin 117) ≠ 1), hrows, hwidth] at hm₂
    rw [hblocks] at hm₃
    unfold publishFromDimensionsCost
    nlinarith only [hm₂, hm₃]
  · refine (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by rw [hclear]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h1 : k = (1 : Fin 117)
    · subst k; simp [hclean 1 (by simp)]
    · by_cases h2 : k = (2 : Fin 117)
      · subst k; simp [hclean 2 (by simp)]
      · simp [S₃, S₂, S₁, result, Function.update_apply, h1, h2]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
