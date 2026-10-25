module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReciprocalNumerator
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealDivision
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReciprocalCrop

/-! # Generate and encode the reciprocal from the retained positive corner

The power numerator, division, runtime-width conversion and release all execute.
The only resulting tape change is the scalar word on initially empty tape 96.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateReciprocal : Pr P₀ 117 Q A U :=
  .seq generateReciprocalNumerator
    (.seq divideRealWords (.seq (uclear 96) cropReciprocal))

theorem generateReciprocal_exec (hA : 4 ≤ A) (P n q W y : ℕ)
    (hn : 1 ≤ n) (hd : q + P * n < W) (hw : 2 * q + 8 ≤ W)
    (hy : y < 2 ^ W) (hy0 : 0 < y)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailD : List (Fin (A + 4)))
    (hP : (S.R 114).length = P) (hnR : (S.R 116).length = n)
    (hq : (S.R 112).length = q) (hW : (S.R 94).length = W)
    (hden : S.R 110 = csyms A W (⟨(y : ℤ), 0⟩ : GaussianInt) ++ tailD)
    (hfresh : ∀ k ∈ [(0 : Fin 117), 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12,
      96, 97, 98, 99, 104, 105, 106, 107, 115], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ W * (12 * W + 128) + 6 * (2 * q + 8) + 4 * q + 134 ∧
      Exec body generateReciprocal (mk v S) m
        (mk v' { S with R := (Function.update S.R 96
          (csyms A (2 * q + 8) (⟨(((2 ^ (q + P * n)) / y : ℕ) : ℤ), 0⟩ : GaussianInt))) }) := by
  let x := 2 ^ (q + P * n)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := generateReciprocalNumerator_exec (body := body)
    P n q W hn hd v S hP hnR hq hW
    (fun k hk => hfresh k ((by decide : [(97 : Fin 117), 99, 104, 105, 106, 107].Sublist
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 96, 97, 98, 99, 104, 105, 106, 107, 115]).subset hk))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 96 (csyms A W (⟨(x : ℤ), 0⟩ : GaussianInt)) }
  have he₁' : Exec body generateReciprocalNumerator (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁, x, hfresh 96 (by simp)] using he₁
  have hx : x < 2 ^ W := Nat.pow_lt_pow_right (by decide) hd
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := divideRealWords_exec (body := body) hA W x y hx hy hy0 v₁ S₁ [] tailD
    (by simpa [S₁] using hW) (by simp [S₁]) (by simpa [S₁] using hden) (by
      intro k hk
      have hne : k ≠ 96 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [S₁, hne] using hfresh k ((by decide :
        [(0 : Fin 117), 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12].Sublist
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 96, 97, 98, 99, 104, 105, 106, 107, 115]).subset hk))
  let z : GaussianInt := ⟨((x / y : ℕ) : ℤ), 0⟩
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 115 (csyms A W z) }
  have he₂' : Exec body divideRealWords (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂, S₁, z, hfresh 115 (by simp)] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 96 v₂ S₂
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 96 [] }
  obtain ⟨v₄, hu₄, he₄⟩ := cropReciprocal_exec (body := body) q W hw z v₃ S₃
    (by simpa [S₃, S₂, S₁] using hq) (by simp [S₃, S₂]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;>
        simpa [S₃, S₂, S₁] using hfresh _ (by simp))
  refine ⟨v₄, m₁ + (m₂ + ((2 * W + 2) + (2 * W + 6 * (2 * q + 8) + 4 * q + 15))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), by nlinarith only [hm₁, hm₂],
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · simp [S₂, S₁]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ho : k = 96
    · subst k; simp [S₃, z, x]
    by_cases hs : k = 115
    · subst k; simp [hfresh 115 (by simp)]
    simp [S₃, S₂, S₁, ho, hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
