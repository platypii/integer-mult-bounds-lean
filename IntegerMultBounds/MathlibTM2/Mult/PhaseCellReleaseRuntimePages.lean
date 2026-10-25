module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSwapCellPayload
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseGeneratorPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseWeightPage

/-! Restore the original borrowed RHS layout and release all retained numerical
pages after cell execution. The runtime precision source is retained. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def releaseRuntimePages : Pr P₀ 117 Q A U :=
  .seq swapCellPayload (.seq (ucopy 100 112 104) (.seq releaseGeneratorPage
    (.seq (uclear 94) (.seq releaseWeightPage (uclear 112)))))

def releaseRuntimePagesCost (L q : ℕ) : ℕ :=
  swapCellPayloadCost L (2 * q + 8) + releaseGeneratorPageCost L q + releaseWeightPageCost L q +
    6 * q + 2 * (2 * q + 8) + 8

theorem releaseRuntimePages_exec (L q : ℕ) (gen outs rhs factors tail : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hL : (S.R 102).length = L) (hq : (S.R 100).length = q) (hw : (S.R 94).length = 2 * q + 8)
    (hgen : gen.length = (2 * L + 1) * (2 * q + 8)) (houts : outs.length = L * (2 * q + 8))
    (hrhs : rhs.length = L * (2 * q + 8)) (hfactors : factors.length = L * (2 * q + 8))
    (hsrc : S.R 110 = gen ++ (outs ++ (rhs ++ (factors ++ tail))))
    (hfresh : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 112], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseRuntimePagesCost L q ∧
      Exec body releaseRuntimePages (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R 94 []) 110 (rhs ++ tail)) }) := by
  let w := 2 * q + 8
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := swapCellPayload_exec (body := body) L w (gen ++ outs) rhs factors tail
    v S hL hw (by simp [hgen, houts, w]; ring) hrhs hfactors (by simpa [List.append_assoc] using hsrc) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 110 ((gen ++ outs) ++ (factors ++ (rhs ++ tail))) }
  obtain ⟨v₂, hu₂, he₂⟩ := ucopy_exec (body := body) (a := 100) (b := 112) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 104 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 112 (List.replicate q tick) }
  have he₂' : Exec body (ucopy 100 112 104) (mk v₁ S₁) (4 * q + 4) (mk v₂ S₂) := by
    simpa [S₂, S₁, hq, hfresh 112 (by simp)] using he₂
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := releaseGeneratorPage_exec (body := body) L q gen
    (outs ++ (factors ++ (rhs ++ tail))) v₂ S₂ (by simpa [S₂, S₁] using hL)
    (by simp [S₂]) hgen (by simp [S₂, S₁, List.append_assoc]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simpa [S₂, S₁] using hfresh _ (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 110 (outs ++ (factors ++ (rhs ++ tail))) }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body 94 v₃ S₃
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 94 [] }
  obtain ⟨v₅, m₅, hu₅, hm₅, he₅⟩ := releaseWeightPage_exec (body := body) L q (outs ++ factors) (rhs ++ tail)
    v₄ S₄ (by simpa [S₄, S₃, S₂, S₁] using hL) (by simp [S₄, S₃, S₂])
    (by simp [houts, hfactors]; ring) (by simp [S₄, S₃, List.append_assoc]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      · simp [S₄]
      all_goals simpa [S₄, S₃, S₂, S₁] using hfresh _ (by simp))
  let S₅ : Stacks 117 A := { S₄ with R := Function.update S₄.R 110 (rhs ++ tail) }
  obtain ⟨v₆, hu₆, he₆⟩ := uclear_exec body 112 v₅ S₅
  have h94 : (S₃.R 94).length = w := by simpa [S₃, S₂, S₁] using hw
  have h112 : (S₅.R 112).length = q := by simp [S₅, S₄, S₃, S₂]
  refine ⟨v₆, m₁ + ((4 * q + 4) + (m₃ + ((2 * w + 2) + (m₅ + (2 * q + 2))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))), ?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast
      (by rw [h94, h112]) ?_⟩
  · unfold releaseRuntimePagesCost
    dsimp only [w] at hm₁ ⊢
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk112 : k = 112
      · subst k; simp [S₅, S₄, S₃, S₂, S₁, hfresh 112 (by simp)]
      simp only [S₅, S₄, S₃, S₂, S₁, Function.update_apply, ite_eq_right hk112]
      by_cases hk94 : k = 94
      · subst k; simp
      by_cases hk110 : k = 110
      · subst k; simp
      simp [hk94, hk110]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
