module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealBits
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv

/-! # Paid positive division of borrowed real setup words

Use the existing restoring binary divider in the clean multiplier bank.
Numerator and divisor prefixes, their suffixes, and all other stacks restore.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def divideRealWords : Pr P₀ 117 Q A U :=
  .seq (copyRealBits 94 96 0 11 12)
    (.seq (copyRealBits 94 110 1 11 12)
      (.seq (bdivmod 0 1 2 3 4 5 6 7 8 9 10)
        (.seq (moveR 2 11 (fun s => pairSym A (symBit s) false))
          (.seq (moveR 11 115 id) (clearWords [0, 1, 3])))))

theorem divideRealWords_exec (hA : 4 ≤ A) (W x y : ℕ)
    (hx : x < 2 ^ W) (hy : y < 2 ^ W) (hy0 : 0 < y)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailN tailD : List (Fin (A + 4)))
    (hwidth : (S.R 94).length = W)
    (hnum : S.R 96 = csyms A W (⟨(x : ℤ), 0⟩ : GaussianInt) ++ tailN)
    (hden : S.R 110 = csyms A W (⟨(y : ℤ), 0⟩ : GaussianInt) ++ tailD)
    (hfresh : ∀ k ∈ [(0 : Fin 117), 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ W * (12 * W + 93) + 75 ∧
      Exec body divideRealWords (mk v S) m
        (mk v' { S with R := (Function.update S.R 115
          (csyms A W (⟨((x / y : ℕ) : ℤ), 0⟩ : GaussianInt) ++ S.R 115)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := copyRealBits_exec (body := body)
    (show [(94 : Fin 117), 96, 0, 11, 12].Nodup by decide) hA W x hx v S tailN hwidth hnum
    (hfresh 0 (by simp)) (hfresh 11 (by simp)) (hfresh 12 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 0 (binSyms W x) }
  obtain ⟨v₂, hu₂, he₂⟩ := copyRealBits_exec (body := body)
    (show [(94 : Fin 117), 110, 1, 11, 12].Nodup by decide) hA W y hy v₁ S₁ tailD
    (by simpa [S₁] using hwidth) (by simpa [S₁] using hden)
    (by simpa [S₁] using hfresh 1 (by simp)) (by simpa [S₁] using hfresh 11 (by simp))
    (by simpa [S₁] using hfresh 12 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 1 (binSyms W y) }
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := bdivmod_exec (body := body)
    (show [(0 : Fin 117), 1, 2, 3, 4, 5, 6, 7, 8, 9].Nodup by decide)
    (show (10 : Fin 117) ≠ 5 by decide) (show (10 : Fin 117) ≠ 4 by decide)
    hx hy hy0 v₂ S₂ (by simp [S₂, S₁]) (by simp [S₂])
    (by simpa [S₂, S₁] using hfresh 4 (by simp)) (by simpa [S₂, S₁] using hfresh 5 (by simp))
    (by simpa [S₂, S₁] using hfresh 6 (by simp)) (by simpa [S₂, S₁] using hfresh 7 (by simp))
    (by simpa [S₂, S₁] using hfresh 8 (by simp)) (by simpa [S₂, S₁] using hfresh 9 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := (Function.update (Function.update S₂.R 2
    (binSyms W (x / y))) 3 (binSyms W (x % y))) }
  have he₃' : Exec body (bdivmod 0 1 2 3 4 5 6 7 8 9 10) (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁, hfresh 2 (by simp), hfresh 3 (by simp)] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body 2 11 (by decide)
    (fun s => pairSym A (symBit s) false) v₃ S₃
  let S₄ : Stacks 117 A := { S₃ with R := movedR S₃.R 2 11 (fun s => pairSym A (symBit s) false) (S₃.R 2) }
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body 11 115 (by decide) id v₄ S₄
  let S₅ : Stacks 117 A := { S₄ with R := movedR S₄.R 11 115 id (S₄.R 11) }
  obtain ⟨v₆, hu₆, he₆⟩ := clearWords_exec (body := body) [0, 1, 3] (by decide) v₅ S₅
  have hsum : ([(0 : Fin 117), 1, 3].map (fun k => (S₅.R k).length)).sum = 3 * W := by
    simp [S₅, S₄, S₃, S₂, S₁, movedR]; ring
  have hlen : (S₄.R 11).length = W := by
    simp [S₄, S₃, S₂, S₁, movedR, hfresh 11 (by simp)]
  have hfit : x / y < 2 ^ W := (Nat.div_le_self x y).trans_lt hx
  refine ⟨v₆, (14 * W + 14) + ((14 * W + 14) + (m₃ + ((2 * W + 2) + ((2 * W + 2) + (6 * W + 7))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))), by nlinarith only [hm₃],
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast ?_ ?_⟩
  · rw [hsum, hlen]; simp [S₃]; ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ho : k = 115
    · subst k
      simp [S₅, S₄, S₃, S₂, S₁, movedR, hfresh 11 (by simp), bits_realWord W (x / y) hfit]
    by_cases h0 : k = 0
    · subst k; simp [hfresh 0 (by simp)]
    by_cases h1 : k = 1
    · subst k; simp [hfresh 1 (by simp)]
    by_cases h3 : k = 3
    · subst k; simp [hfresh 3 (by simp)]
    by_cases h2 : k = 2
    · subst k; simp [S₅, S₄, movedR, hfresh 2 (by simp)]
    by_cases h11 : k = 11
    · subst k; simp [S₅, movedR, hfresh 11 (by simp)]
    simp [S₅, S₄, S₃, S₂, S₁, movedR, ho, h0, h1, h2, h3, h11]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
