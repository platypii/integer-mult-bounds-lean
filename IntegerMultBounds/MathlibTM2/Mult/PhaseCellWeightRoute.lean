module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarRoute

/-! # Route aligned weight streams on the shared 117-tape bank

The row count is derived from the doubled batch header. One generated symbol
counter serves both input transfer and weight-table copying, then is released.
The complete weight source, including its borrowed suffix, is restored.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def routeWeights : Pr P 117 Q A U :=
  .seq (branchWords 108 3 2 103 1 7 8)
    (.seq (unaryProduct 1 94 2 7 8)
      (.seq (takePrefix 2 93 84 7 8)
        (.seq (copyPrefix 2 96 85 26 27) (.seq (uclear 1) (uclear 2)))))

def routeWeightsCost (M L w : ℕ) : ℕ :=
  22 * (M * L * w) + 15 * (M * L) + 17 * M + 34

/-- Generate, use and release every routing count. Weight words retain their
order; the entire persistent table and both native stacks are restored. -/
theorem routeWeights_exec (M L w : ℕ) (xs factors : List GaussianInt)
    (hlen : xs.length = M * L) (hfactors : factors.length = xs.length)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail borrowed : List (Fin (A + 4)))
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hwidth : (S.R 94).length = w)
    (hsrc : S.R 93 = cstream A w xs ++ tail)
    (htable : S.R 96 = cstream A w factors ++ borrowed)
    (hclean : ∀ k ∈ [(1 : Fin 117), 2, 3, 7, 8, 26, 27, 84, 85], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ routeWeightsCost M L w ∧
      Exec body routeWeights (mk v S) m
        (mk v' { S with R := routeR S.R (cstream A w xs) tail (cstream A w factors) }) := by
  have hxs : (cstream A w xs).length = M * L * w := by simp [hlen]
  have hfs : (cstream A w factors).length = M * L * w := by simp [hfactors, hlen]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := branchWords_exec (body := body)
    (batch := 108) (saved := 3) (half := 2) (rows := 103) (words := 1) (buf := 7) (tmp := 8)
    (by decide) M L v S (by omega) hrows (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hclean _ (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 1 (List.replicate (M * L) tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := unaryProduct_exec (body := body)
    (a := 1) (b := 94) (dst := 2) (t₁ := 7) (t₂ := 8) (by decide) v₁ S₁
    (by simp [S₁, hclean 7 (by simp)]) (by simp [S₁, hclean 8 (by simp)])
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 2 (List.replicate (M * L * w) tick) }
  have he₂' : Exec body (unaryProduct 1 94 2 7 8) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₂, S₁, Function.update_self, List.length_replicate,
      Function.update_of_ne (show (94 : Fin 117) ≠ 1 by decide), hwidth,
      Function.update_of_ne (show (2 : Fin 117) ≠ 1 by decide), hclean 2 (by simp), List.append_nil] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := takePrefix_exec (body := body)
    (count := 2) (src := 93) (dst := 84) (buf := 7) (tmp := 8) (by decide)
    v₂ S₂ (cstream A w xs) tail (by simpa [S₂, S₁] using hsrc)
    (by simp [S₂, hxs]) (by simp [S₂, S₁, hclean 7 (by simp)])
    (by simp [S₂, S₁, hclean 8 (by simp)])
  let S₃ : Stacks 117 A := { S₂ with R := (Function.update (Function.update S₂.R 93 tail) 84 (cstream A w xs)) }
  have he₃' : Exec body (takePrefix 2 93 84 7 8) (mk v₂ S₂) (6 * (cstream A w xs).length + 6)
      (mk v₃ S₃) := by
    simpa only [S₃, S₂, S₁, Function.update_of_ne (show (84 : Fin 117) ≠ 2 by decide),
      Function.update_of_ne (show (84 : Fin 117) ≠ 1 by decide), hclean 84 (by simp), List.append_nil] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := copyPrefix_exec (body := body)
    (count := 2) (src := 96) (dst := 85) (saved := 26) (tmp := 27) (by decide)
    v₃ S₃ (cstream A w factors) borrowed (by simpa [S₃, S₂, S₁] using htable)
    (by simp [S₃, S₂, hfs]) (by simp [S₃, S₂, S₁, hclean 26 (by simp)])
    (by simp [S₃, S₂, S₁, hclean 27 (by simp)])
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 85 (cstream A w factors) }
  have he₄' : Exec body (copyPrefix 2 96 85 26 27) (mk v₃ S₃) (10 * (cstream A w factors).length + 10)
      (mk v₄ S₄) := by
    simpa only [S₄, S₃, S₂, S₁, Function.update_of_ne (show (85 : Fin 117) ≠ 84 by decide),
      Function.update_of_ne (show (85 : Fin 117) ≠ 93 by decide),
      Function.update_of_ne (show (85 : Fin 117) ≠ 2 by decide),
      Function.update_of_ne (show (85 : Fin 117) ≠ 1 by decide), hclean 85 (by simp), List.append_nil] using he₄
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body 1 v₄ S₄
  let S₅ : Stacks 117 A := { S₄ with R := Function.update S₄.R 1 [] }
  obtain ⟨v₆, hu₆, he₆⟩ := uclear_exec body 2 v₅ S₅
  have hcount₁ : (S₄.R 1).length = M * L := by simp [S₄, S₃, S₂, S₁]
  have hcount₂ : (S₅.R 2).length = M * L * w := by simp [S₅, S₄, S₃, S₂]
  refine ⟨v₆, m₁ + (m₂ + ((6 * (M * L * w) + 6) +
    ((10 * (M * L * w) + 10) + ((2 * (M * L) + 2) + (2 * (M * L * w) + 2))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))), ?_, ?_⟩
  · have hm₂' : m₂ ≤ (M * L) * (4 * w + 9) + 4 := by simpa [S₁, hwidth] using hm₂
    unfold routeWeightsCost
    nlinarith only [hm₁, hm₂']
  · refine (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅ he₆))))).cast
      (by rw [hxs, hfs, hcount₁, hcount₂]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₂' he₃ he₃' he₄ he₄' he₅ he₆ hu₁ hu₂ hu₃ hu₄ hu₅ hu₆
    funext k
    simp only [S₅, S₄, S₃, S₂, S₁, routeR, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
