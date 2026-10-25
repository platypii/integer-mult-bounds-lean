module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyAfterPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Replicate both generated columns and copy the shared scalar. The numerical
source page is retained; a generated row-symbol counter is passed to packing. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def replicateGeneratorBanks : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 103 94 99 104 105) (.seq (transfer 99 110 107 105)
    (.seq (repeatPrefix 96 108 99 110 113 104 105)
      (.seq (copyAfterPrefix 99 94 110 106 98 104 105)
        (.seq (moveR 107 110 id) (repeatPrefix 96 108 99 110 111 104 105)))))

def replicateGeneratorBanksCost (B L w : ℕ) : ℕ :=
  20 * (B * (L * w)) + 16 * (L * w) + 10 * w + 9 * L + 30 * B + 34

theorem replicateGeneratorBanks_exec (B L w : ℕ) (xs ys a tail : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hbatch : (S.R 96).length = B) (hL : (S.R 103).length = L) (hw : (S.R 94).length = w)
    (hxs : xs.length = L * w) (hys : ys.length = L * w) (ha : a.length = w)
    (hsrc : S.R 110 = xs ++ (ys ++ (a ++ tail)))
    (hfresh : ∀ k ∈ [(98 : Fin 117), 99, 104, 105, 106, 107, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ replicateGeneratorBanksCost B L w ∧
      Exec body replicateGeneratorBanks (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update (Function.update S.R
          99 (List.replicate (L * w) tick)) 106 a)
          111 ((List.replicate B xs).flatten ++ S.R 111))
          113 ((List.replicate B ys).flatten ++ S.R 113)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(103 : Fin 117), 94, 99, 104, 105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 99 (List.replicate (L * w) tick) }
  have he₁' : Exec body (unaryProduct 103 94 99 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁, hL, hw, hfresh 99 (by simp)] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := transfer_exec (body := body)
    (show [(99 : Fin 117), 110, 107, 105].Nodup by decide) v₁ S₁ xs (ys ++ (a ++ tail))
    (by simpa [S₁] using hsrc) (by simp [S₁, hxs]) (by simpa [S₁] using hfresh 105 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update (Function.update S₁.R 110 (ys ++ (a ++ tail))) 107 xs.reverse) }
  have he₂' : Exec body (transfer 99 110 107 105) (mk v₁ S₁) (4 * (L * w) + 4) (mk v₂ S₂) := by
    simpa [S₂, S₁, hxs, hfresh 107 (by simp)] using he₂
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := repeatPrefix_exec (body := body)
    (show [(96 : Fin 117), 108, 99, 110, 113, 104, 105].Nodup by decide)
    B ys (a ++ tail) v₂ S₂ (by simpa [S₂, S₁] using hbatch) (by simp [S₂, S₁, hys])
    (by simp [S₂]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simpa [S₂, S₁] using hfresh _ (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 113 ((List.replicate B ys).flatten ++ S.R 113) }
  have he₃' : Exec body (repeatPrefix 96 108 99 110 113 104 105) (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := copyAfterPrefix_exec (body := body)
    (show [(99 : Fin 117), 94, 110, 106, 98, 104, 105].Nodup by decide) v₃ S₃ ys a tail
    (by simp [S₃, S₂]) (by simp [S₃, S₂, S₁, hys]) (by simpa [S₃, S₂, S₁, ha] using hw) (by
      simpa [S₃, S₂, S₁] using hfresh 98 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 106 a }
  have he₄' : Exec body (copyAfterPrefix 99 94 110 106 98 104 105) (mk v₃ S₃)
      (6 * (L * w) + 10 * w + 16) (mk v₄ S₄) := by
    simpa [S₄, S₃, S₂, S₁, hys, ha, hfresh 106 (by simp)] using he₄
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body 107 110 (by decide) id v₄ S₄
  let S₅ : Stacks 117 A := { S₄ with R := (Function.update (Function.update S₄.R 107 []) 110 (xs ++ (ys ++ (a ++ tail)))) }
  have he₅' : Exec body (moveR 107 110 id) (mk v₄ S₄) (2 * (L * w) + 2) (mk v₅ S₅) := by
    simpa [S₅, S₄, S₃, S₂, S₁, movedR, hxs] using he₅
  obtain ⟨v₆, m₆, hu₆, hm₆, he₆⟩ := repeatPrefix_exec (body := body)
    (show [(96 : Fin 117), 108, 99, 110, 111, 104, 105].Nodup by decide)
    B xs (ys ++ (a ++ tail)) v₅ S₅ (by simpa [S₅, S₄, S₃, S₂, S₁] using hbatch)
    (by simp [S₅, S₄, S₃, S₂, S₁, hxs]) (by simp [S₅]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simpa [S₅, S₄, S₃, S₂, S₁] using hfresh _ (by simp))
  refine ⟨v₆, m₁ + ((4 * (L * w) + 4) + (m₃ + ((6 * (L * w) + 10 * w + 16) + ((2 * (L * w) + 2) + m₆)))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))), ?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅' he₆))))).cast rfl ?_⟩
  · simp only [hL, hw] at hm₁
    rw [hys] at hm₃
    rw [hxs] at hm₆
    unfold replicateGeneratorBanksCost
    nlinarith only [hm₁, hm₃, hm₆]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk107 : k = 107
      · subst k; simp [S₅, S₄, S₃, S₂, S₁, hfresh 107 (by simp)]
      by_cases hk110 : k = 110
      · subst k; simp [S₅, S₄, S₃, S₂, S₁, hsrc]
      simp only [S₅, S₄, S₃, S₂, S₁, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
