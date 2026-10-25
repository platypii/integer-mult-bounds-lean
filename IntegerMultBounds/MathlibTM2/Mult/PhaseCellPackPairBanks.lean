module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Mult.ChirpReverse
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream

/-! Pack separated pair banks in output-descending/input-ascending order.
The original bank suffixes and every temporary count are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def packPairBanks : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 103 94 96 104 105)
    (.seq (reverseWords 103 108 94 113 110 106 104 105)
      (.seq (releasePrefix 96 113 104 105)
        (.seq (takePrefix 96 111 110 104 105) (uclear 96))))

def packPairBanksCost (L w : ℕ) : ℕ := L * (34 * w + 28) + 24

theorem packPairBanks_exec (w L : ℕ) (X Y : ℕ → GaussianInt)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailY : List (Fin (A + 4)))
    (hw : (S.R 94).length = w) (hL : (S.R 103).length = L)
    (hx : S.R 111 = cstream A w ((List.range L).reverse.map X) ++ tailX)
    (hy : S.R 113 = cstream A w ((List.range L).reverse.map Y) ++ tailY)
    (hfresh : ∀ k ∈ [(96 : Fin 117), 104, 105, 106, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ packPairBanksCost L w ∧
      Exec body packPairBanks (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R 110
          (cstream A w ((List.range L).reverse.map X) ++
            (cstream A w ((List.range L).map Y) ++ S.R 110))) 111 tailX) 113 tailY) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(103 : Fin 117), 94, 96, 104, 105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 96 (List.replicate (L * w) tick) }
  have he₁' : Exec body (unaryProduct 103 94 96 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁, hw, hL, hfresh 96 (by simp)] using he₁
  let words := ((List.range L).reverse.map Y).map (csyms A w)
  obtain ⟨v₂, hu₂, he₂⟩ := reverseWords_exec (body := body)
    (show [(103 : Fin 117), 108, 94, 113, 110, 106, 104, 105].Nodup by decide) w words
    (by intro xs hxs; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hxs; simp)
    v₁ S₁ tailY (by simp [S₁, words, hL])
    (by simpa [S₁, words, cstream, List.flatMap_def] using hy)
    (by simpa [S₁] using hw) (by simpa [S₁] using hfresh 108 (by simp))
    (by simpa [S₁] using hfresh 106 (by simp)) (by simpa [S₁] using hfresh 104 (by simp))
    (by simpa [S₁] using hfresh 105 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update S₁.R 110
    (cstream A w ((List.range L).map Y) ++ S.R 110)) }
  have he₂' : Exec body (reverseWords 103 108 94 113 110 106 104 105) (mk v₁ S₁)
      (L * (16 * w + 19) + 6) (mk v₂ S₂) := by
    simpa [S₂, S₁, words, cstream, List.flatMap_def] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := releasePrefix_exec (body := body)
    (show [(96 : Fin 117), 113, 104, 105].Nodup by decide) v₂ S₂
    (cstream A w ((List.range L).reverse.map Y)) tailY (by simpa [S₂, S₁] using hy)
    (by simp [S₂, S₁]) (by simpa [S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₂, S₁] using hfresh 105 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 113 tailY }
  obtain ⟨v₄, hu₄, he₄⟩ := takePrefix_exec (body := body)
    (show [(96 : Fin 117), 111, 110, 104, 105].Nodup by decide) v₃ S₃
    (cstream A w ((List.range L).reverse.map X)) tailX (by simpa [S₃, S₂, S₁] using hx)
    (by simp [S₃, S₂, S₁]) (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := (Function.update (Function.update S₃.R 111 tailX) 110
    (cstream A w ((List.range L).reverse.map X) ++ S₃.R 110)) }
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body 96 v₄ S₄
  refine ⟨v₅, m₁ + ((L * (16 * w + 19) + 6) + ((6 * (L * w) + 6) + ((6 * (L * w) + 6) + (2 * (L * w) + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast (by simp [S₄, S₃, S₂, S₁]) ?_⟩
  · simp only [hw, hL] at hm₁
    unfold packPairBanksCost
    nlinarith only [hm₁]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk96 : k = 96
      · subst k; simp [S₄, S₃, S₂, S₁, hfresh 96 (by simp)]
      simp only [S₄, S₃, S₂, S₁, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
