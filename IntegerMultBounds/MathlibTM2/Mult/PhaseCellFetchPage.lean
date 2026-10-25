module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPageAddress
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBranchWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyAfterPrefix

/-! # Fetch a page behind a fixed number of banks and a scalar

All addressing counts come from retained dimensions. The complete source page,
including its arbitrary suffix, is restored exactly after the copy.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def fetchPage (banks : ℕ) : Pr P 117 Q A U :=
  .seq (branchWords 108 3 2 103 1 7 8)
    (.seq (unaryProduct 1 94 2 7 8)
      (.seq (pageAddress banks 2 94 3 26)
        (.seq (copyAfterPrefix 3 2 110 96 112 26 27) (clearWords [1, 2, 3]))))

def fetchPageCost (banks M L w : ℕ) : ℕ :=
  (16 + 12 * banks) * (M * L * w) + 15 * (M * L) + 17 * M + 12 * w + 4 * banks + 42

theorem fetchPage_exec (banks M L w : ℕ) (pre table tail : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hbatch : (S.R 108).length = 2 * M) (hrows : (S.R 103).length = L) (hwidth : (S.R 94).length = w)
    (hpre : pre.length = banks * (M * L * w) + w) (htable : table.length = M * L * w)
    (hsrc : S.R 110 = pre ++ (table ++ tail))
    (hclean : ∀ k ∈ [(1 : Fin 117), 2, 3, 7, 8, 26, 27, 96, 112], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ fetchPageCost banks M L w ∧
      Exec body (fetchPage banks) (mk v S) m
        (mk v' { S with R := Function.update S.R 96 table }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := branchWords_exec (body := body)
    (batch := 108) (saved := 3) (half := 2) (rows := 103) (words := 1) (buf := 7) (tmp := 8)
    (by decide) M L v S hbatch hrows (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hclean _ (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 1 (List.replicate (M * L) tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := unaryProduct_exec (body := body)
    (a := 1) (b := 94) (dst := 2) (t₁ := 7) (t₂ := 8) (by decide) v₁ S₁
    (by simp [S₁, hclean 7 (by simp)]) (by simp [S₁, hclean 8 (by simp)])
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 2 (List.replicate (M * L * w) tick) }
  have he₂' : Exec body (unaryProduct 1 94 2 7 8) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₁, Function.update_self, List.length_replicate,
      Function.update_of_ne (by decide : (94 : Fin 117) ≠ 1), hwidth,
      Function.update_of_ne (by decide : (2 : Fin 117) ≠ 1), hclean 2 (by simp), List.append_nil] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := pageAddress_exec (body := body)
    (bank := 2) (width := 94) (skip := 3) (saved := 26) (by decide) banks v₂ S₂
    (by simp [S₂, S₁, hclean 3 (by simp)]) (by simp [S₂, S₁, hclean 26 (by simp)])
  let skip := (List.replicate banks (List.replicate (M * L * w) tick).reverse).flatten ++ (S.R 94).reverse
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 3 skip }
  have hskip : skip.length = pre.length := by simp [skip, hwidth, hpre]
  have he₃' : Exec body (pageAddress banks 2 94 3 26) (mk v₂ S₂)
      (banks * (4 * (M * L * w) + 4) + 4 * w + 5) (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁, skip, hwidth] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := copyAfterPrefix_exec (body := body)
    (skip := 3) (width := 2) (src := 110) (dst := 96) (savedPrefix := 112) (savedWord := 26) (tmp := 27)
    (by decide) v₃ S₃ pre table tail
    (by simpa [S₃, S₂, S₁] using hsrc) (by simp [S₃, hskip])
    (by simp [S₃, S₂, htable])
    (by simp [S₃, S₂, S₁, hclean 112 (by simp)])
    (by simp [S₃, S₂, S₁, hclean 26 (by simp)])
    (by simp [S₃, S₂, S₁, hclean 27 (by simp)])
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 96 table }
  have he₄' : Exec body (copyAfterPrefix 3 2 110 96 112 26 27) (mk v₃ S₃)
      (6 * pre.length + 10 * table.length + 16) (mk v₄ S₄) := by
    simpa only [S₃, S₂, S₁, Function.update_of_ne (by decide : (96 : Fin 117) ≠ 3),
      Function.update_of_ne (by decide : (96 : Fin 117) ≠ 2),
      Function.update_of_ne (by decide : (96 : Fin 117) ≠ 1), hclean 96 (by simp), List.append_nil] using he₄
  obtain ⟨v₅, hu₅, he₅⟩ := clearWords_exec (body := body) [1, 2, 3] (by decide) v₄ S₄
  have hclear : 2 * (([1, 2, 3] : List (Fin 117)).map (fun k => (S₄.R k).length)).sum +
      2 * ([1, 2, 3] : List (Fin 117)).length + 1 =
      2 * (M * L + M * L * w + pre.length) + 7 := by
    simp [S₄, S₃, S₂, S₁, hskip, Nat.add_assoc]
  refine ⟨v₅, m₁ + (m₂ + ((banks * (4 * (M * L * w) + 4) + 4 * w + 5) +
    ((6 * pre.length + 10 * table.length + 16) + (2 * (M * L + M * L * w + pre.length) + 7)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_, ?_⟩
  · simp only [S₁, Function.update_self, List.length_replicate,
      Function.update_of_ne (by decide : (94 : Fin 117) ≠ 1), hwidth] at hm₂
    rw [hpre, htable]
    unfold fetchPageCost
    nlinarith only [hm₁, hm₂]
  · refine (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' he₅)))).cast (by rw [hclear]) ?_
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
      · by_cases h3 : k = (3 : Fin 117)
        · subst k; simp [hclean 3 (by simp)]
        · simp [S₄, S₃, S₂, S₁, Function.update_apply, h1, h2, h3]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
