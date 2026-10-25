module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFetchPage

/-! # Stage owned input copies from a preserved per-call payload

The RHS and input reciprocal table follow three banks plus the scalar. They
are borrowed per-call payload, not data shared across replicas by a setup key.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def stagePayload : Pr P 117 Q A U :=
  .seq (fetchPage 3) (.seq (.seq (moveR 96 26 id) (moveR 26 93 id)) (fetchPage 4))

def stagePayloadCost (M L w : ℕ) : ℕ :=
  fetchPageCost 3 M L w + 4 * (M * L * w) + 4 + fetchPageCost 4 M L w

theorem stagePayload_exec (M L w : ℕ) (pre rhs factors tail : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hbatch : (S.R 108).length = 2 * M) (hrows : (S.R 103).length = L) (hwidth : (S.R 94).length = w)
    (hpre : pre.length = 3 * (M * L * w) + w)
    (hrhs : rhs.length = M * L * w) (hfactors : factors.length = M * L * w)
    (hsrc : S.R 110 = pre ++ (rhs ++ (factors ++ tail)))
    (hclean : ∀ k ∈ [(1 : Fin 117), 2, 3, 7, 8, 26, 27, 96, 112], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ stagePayloadCost M L w ∧
      Exec body stagePayload (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R 93 (rhs ++ S.R 93)) 96 factors) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := fetchPage_exec (body := body) 3 M L w pre rhs (factors ++ tail)
    v S hbatch hrows hwidth hpre hrhs hsrc hclean
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 96 rhs }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body 96 26 (by decide) id v₁ S₁
  let S₂ : Stacks 117 A := { S₁ with R := movedR S₁.R 96 26 id (S₁.R 96) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body 26 93 (by decide) id v₂ S₂
  let S₃ : Stacks 117 A := { S with R := Function.update S.R 93 (rhs ++ S.R 93) }
  have he₂₃ : Exec body (.seq (moveR 96 26 id) (moveR 26 93 id)) (mk v₁ S₁)
      (4 * (M * L * w) + 4) (mk v₃ S₃) := by
    refine (Exec.seq he₂ he₃).cast ?_ ?_
    · simp [S₂, S₁, movedR, hclean 26 (by simp), hrhs]; omega
    · congr 1
      ext1
      · rfl
      · rfl
      · rfl
      funext k
      by_cases h96 : k = (96 : Fin 117)
      · subst k; simp [S₂, S₁, S₃, movedR, hclean 96 (by simp)]
      · by_cases h26 : k = (26 : Fin 117)
        · subst k; simp [S₂, S₁, S₃, movedR, hclean 26 (by simp)]
        · simp [S₂, S₁, S₃, movedR, Function.update_apply, h96, h26, hclean 26 (by simp)]
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := fetchPage_exec (body := body) 4 M L w (pre ++ rhs) factors tail
    v₃ S₃ (by simpa [S₃] using hbatch) (by simpa [S₃] using hrows) (by simpa [S₃] using hwidth)
    (by simp [hpre, hrhs]; omega) hfactors (by simpa [S₃, List.append_assoc] using hsrc)
    (by
      intro k hk
      have hn : k ≠ (93 : Fin 117) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [S₃, hn] using hclean k hk)
  exact ⟨v₄, m₁ + ((4 * (M * L * w) + 4) + m₄), hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    by unfold stagePayloadCost; omega, Exec.seq he₁ (Exec.seq he₂₃ he₄)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
