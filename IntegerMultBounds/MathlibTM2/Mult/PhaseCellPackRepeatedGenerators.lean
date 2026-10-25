module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix

/-! Pack replicated generator columns and one shared scalar, then release the
single-cell source page and every generated row/symbol count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def packRepeatedGenerators : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 96 99 97 104 105) (.seq (umul 2 99 98 104)
    (.seq (uadd 94 98 104) (.seq (releasePrefix 98 110 104 105)
      (.seq (takePrefix 94 106 110 104 105) (.seq (takePrefix 97 113 110 104 105)
        (.seq (takePrefix 97 111 110 104 105) (clearWords [97, 98, 99])))))))

def packRepeatedGeneratorsCost (B L w : ℕ) : ℕ :=
  18 * (B * (L * w)) + 22 * (L * w) + 18 * w + 9 * B + 43

theorem packRepeatedGenerators_exec (B L w : ℕ) (xs ys a tail tailX tailY : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hbatch : (S.R 96).length = B) (hcount : (S.R 99).length = L * w) (hw : (S.R 94).length = w)
    (hxs : xs.length = L * w) (hys : ys.length = L * w) (ha : a.length = w)
    (hsrc : S.R 110 = xs ++ (ys ++ (a ++ tail)))
    (hx : S.R 111 = (List.replicate B xs).flatten ++ tailX)
    (hy : S.R 113 = (List.replicate B ys).flatten ++ tailY) (hscalar : S.R 106 = a)
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 104, 105], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ packRepeatedGeneratorsCost B L w ∧
      Exec body packRepeatedGenerators (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update (Function.update
          (Function.update S.R 99 []) 106 []) 111 tailX) 113 tailY) 110
          ((List.replicate B xs).flatten ++ ((List.replicate B ys).flatten ++ (a ++ tail)))) }) := by
  have hrepX : (List.replicate B xs).flatten.length = B * (L * w) := by simp [List.length_flatten, hxs]
  have hrepY : (List.replicate B ys).flatten.length = B * (L * w) := by simp [List.length_flatten, hys]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(96 : Fin 117), 99, 97, 104, 105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 97 (List.replicate (B * (L * w)) tick) }
  have he₁' : Exec body (unaryProduct 96 99 97 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁, hbatch, hcount, hfresh 97 (by simp)] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := umul_exec (body := body) 2 (a := 99) (b := 98) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 104 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 98 (List.replicate (2 * (L * w)) tick) }
  have he₂' : Exec body (umul 2 99 98 104) (mk v₁ S₁) (4 * (L * w) + 4) (mk v₂ S₂) := by
    simpa [S₂, S₁, hcount, hfresh 98 (by simp)] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uadd_exec (body := body) (a := 94) (b := 98) (t := 104)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂, S₁] using hfresh 104 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 98 (List.replicate ((2 * L + 1) * w) tick) }
  have he₃' : Exec body (uadd 94 98 104) (mk v₂ S₂) (4 * w + 4) (mk v₃ S₃) := by
    have heq : w + 2 * (L * w) = (2 * L + 1) * w := by ring
    simpa [S₃, S₂, S₁, hw, List.replicate_append_replicate, heq] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := releasePrefix_exec (body := body)
    (show [(98 : Fin 117), 110, 104, 105].Nodup by decide) v₃ S₃ (xs ++ (ys ++ a)) tail
    (by simpa [S₃, S₂, S₁, List.append_assoc] using hsrc)
    (by simp [S₃, hxs, hys, ha]; ring)
    (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp)) (by simpa [S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 110 tail }
  obtain ⟨v₅, hu₅, he₅⟩ := takePrefix_exec (body := body)
    (show [(94 : Fin 117), 106, 110, 104, 105].Nodup by decide) v₄ S₄ a []
    (by simpa [S₄, S₃, S₂, S₁] using hscalar) (by simpa [S₄, S₃, S₂, S₁, ha] using hw)
    (by simpa [S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₄, S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₅ : Stacks 117 A := { S₄ with R := (Function.update (Function.update S₄.R 106 []) 110 (a ++ tail)) }
  obtain ⟨v₆, hu₆, he₆⟩ := takePrefix_exec (body := body)
    (show [(97 : Fin 117), 113, 110, 104, 105].Nodup by decide) v₅ S₅ (List.replicate B ys).flatten tailY
    (by simpa [S₅, S₄, S₃, S₂, S₁] using hy) (by simp [S₅, S₄, S₃, S₂, S₁, hrepY])
    (by simpa [S₅, S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₅, S₄, S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₆ : Stacks 117 A := { S₅ with R := (Function.update (Function.update S₅.R 113 tailY) 110
    ((List.replicate B ys).flatten ++ S₅.R 110)) }
  obtain ⟨v₇, hu₇, he₇⟩ := takePrefix_exec (body := body)
    (show [(97 : Fin 117), 111, 110, 104, 105].Nodup by decide) v₆ S₆ (List.replicate B xs).flatten tailX
    (by simpa [S₆, S₅, S₄, S₃, S₂, S₁] using hx) (by simp [S₆, S₅, S₄, S₃, S₂, S₁, hrepX])
    (by simpa [S₆, S₅, S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₆, S₅, S₄, S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₇ : Stacks 117 A := { S₆ with R := (Function.update (Function.update S₆.R 111 tailX) 110
    ((List.replicate B xs).flatten ++ S₆.R 110)) }
  obtain ⟨v₈, hu₈, he₈⟩ := clearWords_exec (body := body) [97, 98, 99] (by decide) v₇ S₇
  have hsum : ([(97 : Fin 117), 98, 99].map (fun k => (S₇.R k).length)).sum =
      B * (L * w) + (2 * L + 1) * w + L * w := by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, hcount, Nat.add_assoc]
  refine ⟨v₈, m₁ + ((4 * (L * w) + 4) + ((4 * w + 4) +
    ((6 * ((2 * L + 1) * w) + 6) + ((6 * w + 6) + ((6 * (B * (L * w)) + 6) +
      ((6 * (B * (L * w)) + 6) + (2 * (B * (L * w) + (2 * L + 1) * w + L * w) + 7))))))),
    hu₈.trans (hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))))), ?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆ (Exec.seq he₇ he₈))))))).cast ?_ ?_⟩
  · simp only [hbatch, hcount] at hm₁
    unfold packRepeatedGeneratorsCost
    nlinarith only [hm₁]
  · simp only [List.length_append, hxs, hys, ha, hrepX, hrepY, hsum, List.length_cons, List.length_nil]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk97 : k = 97
      · subst k; simp [hfresh 97 (by simp)]
      by_cases hk98 : k = 98
      · subst k; simp [hfresh 98 (by simp)]
      simp only [S₇, S₆, S₅, S₄, S₃, S₂, S₁, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
