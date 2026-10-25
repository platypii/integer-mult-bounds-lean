module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyAfterPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Fetch the retained reciprocal word with generated skip counts -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

/-- The source prefix is saved on a released batch-work port and restored exactly. -/
def fetchScalar : Pr P 117 Q A U :=
  .seq (unaryProduct 108 103 1 7 8)
    (.seq (unaryProduct 1 94 2 7 8)
      (.seq (copyAfterPrefix 2 94 110 96 112 26 27) (clearWords [1, 2])))

def fetchScalarCost (B L w : ℕ) : ℕ :=
  12 * (B * L * w) + 15 * (B * L) + 9 * B + 10 * w + 29

/-- All skip-count generation, copying and cleanup is charged. Only the fetched
scalar port changes; the raw generators and borrowed suffix survive exactly. -/
theorem fetchScalar_exec (B L w : ℕ) (pre tail : List (Fin (A + 4))) (a : GaussianInt)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hbatch : (S.R 108).length = B) (hrows : (S.R 103).length = L) (hwidth : (S.R 94).length = w)
    (hlen : pre.length = B * L * w) (hsrc : S.R 110 = pre ++ (csyms A w a ++ tail))
    (hclean : ∀ k ∈ [(1 : Fin 117), 2, 7, 8, 26, 27, 96, 112], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ fetchScalarCost B L w ∧
      Exec body fetchScalar (mk v S) m
        (mk v' { S with R := Function.update S.R 96 (csyms A w a) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (a := 108) (b := 103) (dst := 1) (t₁ := 7) (t₂ := 8) (by decide) v S
    (hclean _ (by simp)) (hclean _ (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 1 (List.replicate (B * L) tick) }
  have he₁' : Exec body (unaryProduct 108 103 1 7 8) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hbatch, hrows, hclean 1 (by simp), List.append_nil] using he₁
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := unaryProduct_exec (body := body)
    (a := 1) (b := 94) (dst := 2) (t₁ := 7) (t₂ := 8) (by decide) v₁ S₁
    (by simp [S₁, hclean 7 (by simp)]) (by simp [S₁, hclean 8 (by simp)])
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 2 (List.replicate (B * L * w) tick) }
  have he₂' : Exec body (unaryProduct 1 94 2 7 8) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₁, Function.update_self, List.length_replicate,
      Function.update_of_ne (show (94 : Fin 117) ≠ 1 by decide), hwidth,
      Function.update_of_ne (show (2 : Fin 117) ≠ 1 by decide), hclean 2 (by simp), List.append_nil] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := copyAfterPrefix_exec (body := body)
    (skip := 2) (width := 94) (src := 110) (dst := 96) (savedPrefix := 112) (savedWord := 26) (tmp := 27)
    (by decide) v₂ S₂ pre (csyms A w a) tail
    (by simpa [S₂, S₁] using hsrc) (by simp [S₂, hlen])
    (by simpa [S₂, S₁] using hwidth)
    (by simp [S₂, S₁, hclean 112 (by simp)]) (by simp [S₂, S₁, hclean 26 (by simp)])
    (by simp [S₂, S₁, hclean 27 (by simp)])
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 96 (csyms A w a) }
  have hsym : (csyms A w a).length = w := by simp [csyms]
  have he₃' : Exec body (copyAfterPrefix 2 94 110 96 112 26 27) (mk v₂ S₂)
      (6 * pre.length + 10 * w + 16) (mk v₃ S₃) := by
    simpa only [S₂, S₁, Function.update_of_ne (show (96 : Fin 117) ≠ 2 by decide),
      Function.update_of_ne (show (96 : Fin 117) ≠ 1 by decide), hclean 96 (by simp),
      List.append_nil, hsym] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := clearWords_exec (body := body) [1, 2] (by decide) v₃ S₃
  have hclear : 2 * (([1, 2] : List (Fin 117)).map (fun k => (S₃.R k).length)).sum +
      2 * ([1, 2] : List (Fin 117)).length + 1 = 2 * (B * L + B * L * w) + 5 := by
    simp [S₃, S₂, S₁]
  refine ⟨v₄, m₁ + (m₂ + ((6 * pre.length + 10 * w + 16) + (2 * (B * L + B * L * w) + 5))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_⟩
  · rw [hbatch, hrows] at hm₁
    simp only [S₁, Function.update_self, List.length_replicate,
      Function.update_of_ne (show (94 : Fin 117) ≠ 1 by decide), hwidth] at hm₂
    rw [hlen]
    unfold fetchScalarCost
    nlinarith only [hm₁, hm₂]
  · refine (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast (by rw [hclear]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h1 : k = (1 : Fin 117)
    · subst k
      simp [hclean 1 (by simp)]
    · by_cases h2 : k = (2 : Fin 117)
      · subst k
        simp [hclean 2 (by simp)]
      · simp [S₃, S₂, S₁, Function.update_apply, h1, h2]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
