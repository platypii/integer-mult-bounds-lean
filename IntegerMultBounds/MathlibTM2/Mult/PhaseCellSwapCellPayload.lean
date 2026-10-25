module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSwapAfterPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Place a single-cell RHS between output weights and reciprocal input weights.
All offsets are generated from L and the runtime word width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def swapCellPayload : Pr P₀ 117 Q A U :=
  .seq (unaryProduct 102 94 99 104 105) (.seq (umul 3 99 97 104)
    (.seq (uadd 94 97 104) (.seq (swapAfterPrefix 97 99 110 98 106 107 105)
      (clearWords [97, 99]))))

def swapCellPayloadCost (L w : ℕ) : ℕ := L * (46 * w + 9) + 12 * w + 35

theorem swapCellPayload_exec (L w : ℕ) (pre xs ys tail : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hL : (S.R 102).length = L) (hw : (S.R 94).length = w)
    (hpre : pre.length = (3 * L + 1) * w) (hx : xs.length = L * w) (hy : ys.length = L * w)
    (hsrc : S.R 110 = pre ++ (xs ++ (ys ++ tail)))
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105, 106, 107], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ swapCellPayloadCost L w ∧
      Exec body swapCellPayload (mk v S) m
        (mk v' { S with R := Function.update S.R 110 (pre ++ (ys ++ (xs ++ tail))) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [(102 : Fin 117), 94, 99, 104, 105].Nodup by decide) v S
    (hfresh 104 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 99 (List.replicate (L * w) tick) }
  have he₁' : Exec body (unaryProduct 102 94 99 104 105) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁, hL, hw, hfresh 99 (by simp)] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := umul_exec (body := body) 3 (a := 99) (b := 97) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 104 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 97 (List.replicate (3 * (L * w)) tick) }
  have he₂' : Exec body (umul 3 99 97 104) (mk v₁ S₁) (4 * (L * w) + 4) (mk v₂ S₂) := by
    simpa [S₂, S₁, hfresh 97 (by simp)] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uadd_exec (body := body) (a := 94) (b := 97) (t := 104)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂, S₁] using hfresh 104 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 97 (List.replicate ((3 * L + 1) * w) tick) }
  have he₃' : Exec body (uadd 94 97 104) (mk v₂ S₂) (4 * w + 4) (mk v₃ S₃) := by
    have hsum : w + 3 * (L * w) = (3 * L + 1) * w := by ring
    simpa [S₃, S₂, S₁, hw, List.replicate_append_replicate, hsum] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := swapAfterPrefix_exec (body := body)
    (show [(97 : Fin 117), 99, 110, 98, 106, 107, 105].Nodup by decide) v₃ S₃ pre xs ys tail
    (by simpa [S₃, S₂, S₁] using hsrc) (by simp [S₃, hpre])
    (by simp [S₃, S₂, S₁, hx]) (by simp [S₃, S₂, S₁, hy]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simpa [S₃, S₂, S₁] using hfresh _ (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 110 (pre ++ (ys ++ (xs ++ tail))) }
  obtain ⟨v₅, hu₅, he₅⟩ := clearWords_exec (body := body) [97, 99] (by decide) v₄ S₄
  have hsum : ([(97 : Fin 117), 99].map (fun k => (S₄.R k).length)).sum = (4 * L + 1) * w := by
    simp [S₄, S₃, S₂, S₁]
    ring
  refine ⟨v₅, m₁ + ((4 * (L * w) + 4) + ((4 * w + 4) +
      ((6 * pre.length + 12 * xs.length + 18) + (2 * ((4 * L + 1) * w) + 5)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ he₅)))).cast
      (by rw [hsum]; rfl) ?_⟩
  · simp only [hL, hw] at hm₁
    unfold swapCellPayloadCost
    rw [hpre, hx]
    nlinarith only [hm₁]
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
      simp [S₄, S₃, S₂, S₁, Function.update_apply, hk97, hk99]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
