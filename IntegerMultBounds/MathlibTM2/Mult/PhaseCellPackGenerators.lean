module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix

/-! # Assemble the retained runtime generator page and release the raw column

The first generator, shifted reverse and reciprocal are moved in order above
the original borrowed payload. Raw setup words and temporary counts are released.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def packGenerators : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 102 94 99 104 105)
    (.seq (releasePrefix 99 110 104 105)
      (.seq (uclear 99)
        (.seq (umul 2 112 98 104)
          (.seq (.act (pushN 98 (fun _ => tick) 8 .done))
            (.seq (takePrefix 98 96 110 104 105)
              (.seq (unaryProduct 102 98 99 104 105)
                (.seq (takePrefix 99 113 110 104 105)
                  (.seq (takePrefix 99 111 110 104 105) (clearWords [99, 98])))))))))

def packGeneratorsCost (L W q : ℕ) : ℕ :=
  12 * (L * W) + 18 * (L * (2 * q + 8)) + 18 * L + 8 * (2 * q + 8) + 4 * q + 44

theorem packGenerators_exec (L W q : ℕ) (raw xs ys : List GaussianInt) (a : GaussianInt)
    (hraw : raw.length = L) (hxs : xs.length = L) (hys : ys.length = L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail tailX tailY : List (Fin (A + 4)))
    (hrows : (S.R 102).length = L) (hW : (S.R 94).length = W) (hq : (S.R 112).length = q)
    (hsrc : S.R 110 = cstream A W raw ++ tail)
    (hx : S.R 111 = cstream A (2 * q + 8) xs ++ tailX)
    (hy : S.R 113 = cstream A (2 * q + 8) ys ++ tailY)
    (ha : S.R 96 = csyms A (2 * q + 8) a)
    (hfresh : ∀ k ∈ [(98 : Fin 117), 99, 104, 105], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ packGeneratorsCost L W q ∧
      Exec body packGenerators (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update
          (Function.update S.R 110 (cstream A (2 * q + 8) xs ++
            (cstream A (2 * q + 8) ys ++ (csyms A (2 * q + 8) a ++ tail)) ))
          111 tailX) 113 tailY) 96 []) }) := by
  let w := 2 * q + 8
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(102 : Fin 117), 94, 99, 104, 105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 99 (List.replicate (L * W) tick) }
  have he₁' : Exec body (unaryProduct 102 94 99 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁, hrows, hW, hfresh 99 (by simp)] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := releasePrefix_exec (body := body)
    (show [(99 : Fin 117), 110, 104, 105].Nodup by decide) v₁ S₁ (cstream A W raw) tail
    (by simpa [S₁] using hsrc) (by simp [S₁, hraw])
    (by simpa [S₁] using hfresh 104 (by simp)) (by simpa [S₁] using hfresh 105 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 110 tail }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 99 v₂ S₂
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 99 [] }
  obtain ⟨v₄, hu₄, he₄⟩ := umul_exec (body := body) 2 (a := 112) (b := 98) (t := 104)
    (by decide) (by decide) (by decide) v₃ S₃ (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 98 (List.replicate (2 * q) tick) }
  have he₄' : Exec body (umul 2 112 98 104) (mk v₃ S₃) (4 * q + 4) (mk v₄ S₄) := by
    simpa [S₄, S₃, S₂, S₁, hq, hfresh 98 (by simp)] using he₄
  let S₅ : Stacks 117 A := { S₄ with R := Function.update S₄.R 98 (List.replicate w tick) }
  have he₅ : Exec body (.act (pushN 98 (fun _ => tick) 8 .done)) (mk v₄ S₄) 1 (mk v₄ S₅) := by
    have he := Exec.act (body := body) (pushN 98 (fun _ => tick) 8 .done) (mk v₄ S₄)
    rw [pushN_run] at he
    simpa only [S₅, S₄, Action.run, Function.update_self, List.replicate_append_replicate,
      show 8 + 2 * q = w by dsimp [w]; omega] using he
  obtain ⟨v₆, hu₆, he₆⟩ := takePrefix_exec (body := body)
    (show [(98 : Fin 117), 96, 110, 104, 105].Nodup by decide) v₄ S₅ (csyms A w a) []
    (by simpa [S₅, S₄, S₃, S₂, S₁] using ha) (by simp [S₅])
    (by simpa [S₅, S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₅, S₄, S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₆ : Stacks 117 A := { S₅ with R := (Function.update (Function.update S₅.R 96 []) 110
    (csyms A w a ++ S₅.R 110)) }
  obtain ⟨v₇, m₇, hu₇, hm₇, he₇⟩ := unaryProduct_exec (body := body)
    (show [(102 : Fin 117), 98, 99, 104, 105].Nodup by decide) v₆ S₆
    (by simpa [S₆, S₅, S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₆, S₅, S₄, S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₇ : Stacks 117 A := { S₆ with R := Function.update S₆.R 99 (List.replicate (L * w) tick) }
  have he₇' : Exec body (unaryProduct 102 98 99 104 105) (mk v₆ S₆) m₇ (mk v₇ S₇) := by
    simpa [S₇, S₆, S₅, S₄, S₃, S₂, S₁, hrows] using he₇
  obtain ⟨v₈, hu₈, he₈⟩ := takePrefix_exec (body := body)
    (show [(99 : Fin 117), 113, 110, 104, 105].Nodup by decide) v₇ S₇ (cstream A w ys) tailY
    (by simpa [S₇, S₆, S₅, S₄, S₃, S₂, S₁] using hy) (by simp [S₇, hys])
    (by simpa [S₇, S₆, S₅, S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₇, S₆, S₅, S₄, S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₈ : Stacks 117 A := { S₇ with R := (Function.update (Function.update S₇.R 113 tailY) 110
    (cstream A w ys ++ S₇.R 110)) }
  obtain ⟨v₉, hu₉, he₉⟩ := takePrefix_exec (body := body)
    (show [(99 : Fin 117), 111, 110, 104, 105].Nodup by decide) v₈ S₈ (cstream A w xs) tailX
    (by simpa [S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁] using hx) (by simp [S₈, S₇, hxs])
    (by simpa [S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₉ : Stacks 117 A := { S₈ with R := (Function.update (Function.update S₈.R 111 tailX) 110
    (cstream A w xs ++ S₈.R 110)) }
  obtain ⟨v₁₀, hu₁₀, he₁₀⟩ := clearWords_exec (body := body) [99, 98] (by decide) v₉ S₉
  have hsum : ([(99 : Fin 117), 98].map (fun k => (S₉.R k).length)).sum = L * w + w := by
    simp [S₉, S₈, S₇, S₆, S₅]
  have hcount : (S₂.R 99).length = L * W := by simp [S₂, S₁]
  have hrows₆ : (S₆.R 102).length = L := by simp [S₆, S₅, S₄, S₃, S₂, S₁, hrows]
  have hw₆ : (S₆.R 98).length = w := by simp [S₆, S₅]
  rw [hrows, hW] at hm₁
  rw [hrows₆, hw₆] at hm₇
  refine ⟨v₁₀, m₁ + ((6 * (L * W) + 6) + ((2 * (L * W) + 2) + ((4 * q + 4) + (1 +
    ((6 * w + 6) + (m₇ + ((6 * (L * w) + 6) + ((6 * (L * w) + 6) + (2 * (L * w + w) + 5))))))))),
    hu₁₀.trans (hu₉.trans (hu₈.trans (hu₇.trans (hu₆.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))))))), ?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄' (Exec.seq he₅ (Exec.seq he₆
      (Exec.seq he₇' (Exec.seq he₈ (Exec.seq he₉ he₁₀))))))))).cast ?_ ?_⟩
  · unfold packGeneratorsCost
    dsimp [w] at hm₇ ⊢
    nlinarith only [hm₁, hm₇]
  · rw [hsum, hcount]; simp [hraw, hxs, hys, csyms]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h99 : k = 99
    · subst k; simp [hfresh 99 (by simp)]
    by_cases h98 : k = 98
    · subst k; simp [hfresh 98 (by simp)]
    simp [S₉, S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁, h99, h98, w, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
