module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpReverse
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease

/-! Pack two banks of equal-width rows in forward cell order. Whole-row
reversal preserves each row's internal coefficient and bit order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def packWeightBatch : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 116 64 65 104 105)
    (.seq (reverseWords 116 108 64 113 110 106 104 105)
      (.seq (releasePrefix 65 113 104 105)
        (.seq (reverseWords 116 108 64 95 110 106 104 105)
          (.seq (releasePrefix 65 95 104 105) (uclear 65)))))

def packWeightBatchCost (B r : ℕ) : ℕ := B * (50 * r + 47) + 30

theorem packWeightBatch_exec (r B : ℕ) (X Y : List (List (Fin (A + 4))))
    (hX : X.length = B) (hY : Y.length = B)
    (hxr : ∀ xs ∈ X, xs.length = r) (hyr : ∀ ys ∈ Y, ys.length = r)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailY : List (Fin (A + 4)))
    (hw : (S.R 64).length = r) (hB : (S.R 116).length = B)
    (hx : S.R 95 = X.reverse.flatten ++ tailX) (hy : S.R 113 = Y.reverse.flatten ++ tailY)
    (hfresh : ∀ k ∈ [(65 : Fin 117), 104, 105, 106, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ packWeightBatchCost B r ∧
      Exec body packWeightBatch (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R
          110 (X.flatten ++ Y.flatten ++ S.R 110)) 95 tailX) 113 tailY) }) := by
  have hxlen : X.reverse.flatten.length = B * r := by
    rw [List.length_flatten]
    have hh : X.reverse.map List.length = List.replicate B r := by
      rw [← hX, ← (List.length_reverse (as := X))]
      exact List.map_eq_replicate_iff.mpr (fun xs hxs => hxr xs (List.mem_reverse.mp hxs))
    rw [hh, List.sum_replicate, smul_eq_mul]
  have hylen : Y.reverse.flatten.length = B * r := by
    rw [List.length_flatten]
    have hh : Y.reverse.map List.length = List.replicate B r := by
      rw [← hY, ← (List.length_reverse (as := Y))]
      exact List.map_eq_replicate_iff.mpr (fun ys hys => hyr ys (List.mem_reverse.mp hys))
    rw [hh, List.sum_replicate, smul_eq_mul]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(116 : Fin 117), 64, 65, 104, 105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 65 (List.replicate (B*r) tick) }
  have he₁' : Exec body (unaryProduct 116 64 65 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁, hw, hB, hfresh 65 (by simp)] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := reverseWords_exec (body := body)
    (show [(116 : Fin 117), 108, 64, 113, 110, 106, 104, 105].Nodup by decide) r Y.reverse
    (by intro ys hys; exact hyr ys (List.mem_reverse.mp hys)) v₁ S₁ tailY
    (by simpa [S₁, hY] using hB) (by simpa [S₁] using hy) (by simpa [S₁] using hw)
    (by simpa [S₁] using hfresh 108 (by simp)) (by simpa [S₁] using hfresh 106 (by simp))
    (by simpa [S₁] using hfresh 104 (by simp)) (by simpa [S₁] using hfresh 105 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 110 (Y.flatten ++ S.R 110) }
  have he₂' : Exec body (reverseWords 116 108 64 113 110 106 104 105) (mk v₁ S₁)
      (B*(16*r+19)+6) (mk v₂ S₂) := by simpa [S₂, S₁, hY] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := releasePrefix_exec (body := body)
    (show [(65 : Fin 117), 113, 104, 105].Nodup by decide) v₂ S₂ Y.reverse.flatten tailY
    (by simpa [S₂, S₁] using hy) (by simp [S₂, S₁, hylen])
    (by simpa [S₂, S₁] using hfresh 104 (by simp)) (by simpa [S₂, S₁] using hfresh 105 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 113 tailY }
  obtain ⟨v₄, hu₄, he₄⟩ := reverseWords_exec (body := body)
    (show [(116 : Fin 117), 108, 64, 95, 110, 106, 104, 105].Nodup by decide) r X.reverse
    (by intro xs hxs; exact hxr xs (List.mem_reverse.mp hxs)) v₃ S₃ tailX
    (by simpa [S₃, S₂, S₁, hX] using hB) (by simpa [S₃, S₂, S₁] using hx)
    (by simpa [S₃, S₂, S₁] using hw)
    (by simpa [S₃, S₂, S₁] using hfresh 108 (by simp)) (by simpa [S₃, S₂, S₁] using hfresh 106 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp)) (by simpa [S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 110 (X.flatten ++ Y.flatten ++ S.R 110) }
  have he₄' : Exec body (reverseWords 116 108 64 95 110 106 104 105) (mk v₃ S₃)
      (B*(16*r+19)+6) (mk v₄ S₄) := by simpa [S₄, S₃, S₂, S₁, hX, List.append_assoc] using he₄
  obtain ⟨v₅, hu₅, he₅⟩ := releasePrefix_exec (body := body)
    (show [(65 : Fin 117), 95, 104, 105].Nodup by decide) v₄ S₄ X.reverse.flatten tailX
    (by simpa [S₄, S₃, S₂, S₁] using hx) (by simp [S₄, S₃, S₂, S₁, hxlen])
    (by simpa [S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₄, S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₅ : Stacks 117 A := { S₄ with R := Function.update S₄.R 95 tailX }
  obtain ⟨v₆, hu₆, he₆⟩ := uclear_exec body 65 v₅ S₅
  refine ⟨v₆, m₁ + ((B*(16*r+19)+6) + ((6*(B*r)+6) +
    ((B*(16*r+19)+6) + ((6*(B*r)+6) + (2*(B*r)+2))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))), ?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' (Exec.seq he₅ he₆))))).cast
      (by simp [S₅, S₄, S₃, S₂, S₁, hxlen, hylen]) ?_⟩
  · simp only [hw, hB] at hm₁
    unfold packWeightBatchCost
    nlinarith only [hm₁]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk : k = 65
      · subst k; simp [S₅, S₄, S₃, S₂, S₁, hfresh 65 (by simp)]
      simp only [S₅, S₄, S₃, S₂, S₁, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
