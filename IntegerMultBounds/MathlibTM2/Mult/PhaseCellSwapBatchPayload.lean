module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSwapAfterPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Place the batch RHS between output weights and reciprocal input weights.
All offsets are generated from the batch count, L and the runtime word width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def swapBatchPayload : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 96 103 99 104 105)
    (.seq (unaryProduct 99 94 97 104 105) (.seq (uclear 99)
      (.seq (umul 3 97 99 104) (.seq (uadd 94 99 104)
        (.seq (swapAfterPrefix 99 97 110 98 106 107 105) (clearWords [97, 99]))))))

def swapBatchPayloadCost (B L w : ℕ) : ℕ := B * (L * (46 * w + 15) + 9) + 12 * w + 41

theorem swapBatchPayload_exec (B L w : ℕ) (pre xs ys tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hB : (S.R 96).length = B) (hL : (S.R 103).length = L) (hw : (S.R 94).length = w)
    (hpre : pre.length = (3*(B*L)+1)*w) (hx : xs.length = B*L*w) (hy : ys.length = B*L*w)
    (hsrc : S.R 110 = pre ++ (xs ++ (ys ++ tail)))
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105, 106, 107], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ swapBatchPayloadCost B L w ∧
      Exec body swapBatchPayload (mk v S) m
        (mk v' { S with R := Function.update S.R 110 (pre ++ (ys ++ (xs ++ tail))) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(96 : Fin 117), 103, 99, 104, 105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 99 (List.replicate (B*L) tick) }
  have he₁' : Exec body (unaryProduct 96 103 99 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁, hB, hL, hfresh 99 (by simp)] using he₁
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := unaryProduct_exec (body := body)
    (show [(99 : Fin 117), 94, 97, 104, 105].Nodup by decide) v₁ S₁
    (by simpa [S₁] using hfresh 104 (by simp)) (by simpa [S₁] using hfresh 105 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 97 (List.replicate (B*L*w) tick) }
  have he₂' : Exec body (unaryProduct 99 94 97 104 105) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂, S₁, hw, hfresh 97 (by simp)] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 99 v₂ S₂
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 99 [] }
  obtain ⟨v₄, hu₄, he₄⟩ := umul_exec (body := body) 3 (a := 97) (b := 99) (t := 104)
    (by decide) (by decide) (by decide) v₃ S₃ (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 99 (List.replicate (3*(B*L*w)) tick) }
  have he₄' : Exec body (umul 3 97 99 104) (mk v₃ S₃) (4*(B*L*w)+4) (mk v₄ S₄) := by
    simpa [S₄, S₃, S₂] using he₄
  obtain ⟨v₅, hu₅, he₅⟩ := uadd_exec (body := body) (a := 94) (b := 99) (t := 104)
    (by decide) (by decide) (by decide) v₄ S₄ (by simpa [S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
  let S₅ : Stacks 117 A := { S₄ with R := Function.update S₄.R 99 (List.replicate ((3*(B*L)+1)*w) tick) }
  have he₅' : Exec body (uadd 94 99 104) (mk v₄ S₄) (4*w+4) (mk v₅ S₅) := by
    have hsum : w+3*(B*L*w) = (3*(B*L)+1)*w := by ring
    simpa [S₅, S₄, S₃, S₂, S₁, hw, List.replicate_append_replicate, hsum] using he₅
  obtain ⟨v₆, hu₆, he₆⟩ := swapAfterPrefix_exec (body := body)
    (show [(99 : Fin 117), 97, 110, 98, 106, 107, 105].Nodup by decide) v₅ S₅ pre xs ys tail
    (by simpa [S₅, S₄, S₃, S₂, S₁] using hsrc) (by simp [S₅, hpre])
    (by simp [S₅, S₄, S₃, S₂, hx]) (by simp [S₅, S₄, S₃, S₂, hy]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      all_goals simpa [S₅, S₄, S₃, S₂, S₁] using hfresh _ (by simp))
  let S₆ : Stacks 117 A := { S₅ with R := Function.update S₅.R 110 (pre ++ (ys ++ (xs ++ tail))) }
  obtain ⟨v₇, hu₇, he₇⟩ := clearWords_exec (body := body) [(97 : Fin 117), 99] (by decide) v₆ S₆
  have hsum : ([(97 : Fin 117), 99].map (fun k => (S₆.R k).length)).sum = (4*(B*L)+1)*w := by
    simp [S₆, S₅, S₄, S₃, S₂]
    ring
  refine ⟨v₇, m₁ + (m₂ + ((2*(B*L)+2) + ((4*(B*L*w)+4) + ((4*w+4) +
    ((6*pre.length+12*xs.length+18) + (2*((4*(B*L)+1)*w)+5)))))),
    hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))))), ?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' (Exec.seq he₅' (Exec.seq he₆ he₇)))))).cast
      (by rw [hsum]; simp [S₂, S₁]) ?_⟩
  · simp only [hB, hL] at hm₁
    have hm₂' : m₂ ≤ (B*L)*(4*w+9)+4 := by simpa [S₁, hw] using hm₂
    unfold swapBatchPayloadCost
    rw [hpre, hx]
    nlinarith only [hm₁, hm₂']
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk97 : k = 97
      · subst k; simp [hfresh 97 (by simp)]
      by_cases hk99 : k = 99
      · subst k; simp [hfresh 99 (by simp)]
      simp [S₆, S₅, S₄, S₃, S₂, S₁, Function.update_apply, hk97, hk99]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
