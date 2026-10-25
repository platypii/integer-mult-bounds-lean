module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarRoute

/-! # Release scalar operands and publish the ordered scalar result -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def finish : Pr P 117 Q A U :=
  .seq (uclear 84) (.seq (uclear 85) (.seq (moveR 89 26 id) (moveR 26 93 id)))

/-- Clear both restored operand copies and return the result to the persistent
output tape in original word order. Every arithmetic data port returns empty. -/
theorem finish_stream_exec (w : ℕ) (xs ys factors : List GaussianInt) (hlen : ys.length = xs.length)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hclean : ∀ k ∈ [(26 : Fin 117), 84, 85, 89], S.R k = []) :
    let SR := { S with R := (Function.update
      (routeR S.R (cstream A w xs) tail (cstream A w factors)) 89 (cstream A w ys)) }
    ∃ v', v'.user = v.user ∧
      Exec body finish (mk v SR) (6 * (xs.length * w) + 2 * (factors.length * w) + 8)
        (mk v' { S with R := Function.update S.R 93 (cstream A w ys ++ tail) }) := by
  dsimp only
  let SR : Stacks 117 A := { S with R := (Function.update
    (routeR S.R (cstream A w xs) tail (cstream A w factors)) 89 (cstream A w ys)) }
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body 84 v SR
  let S₁ : Stacks 117 A := { SR with R := Function.update SR.R 84 [] }
  obtain ⟨v₂, hu₂, he₂⟩ := uclear_exec body 85 v₁ S₁
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 85 [] }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body 89 26 (by decide) id v₂ S₂
  let S₃ : Stacks 117 A := { S₂ with R := movedR S₂.R 89 26 id (S₂.R 89) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body 26 93 (by decide) id v₃ S₃
  refine ⟨v₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · simp [S₃, S₂, S₁, SR, routeR, movedR, hlen,
      hclean 26 (by simp)]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ he₄ hu₁ hu₂ hu₃ hu₄
    funext k
    by_cases h93 : k = (93 : Fin 117)
    · subst k
      simp [S₃, S₂, S₁, SR, routeR, movedR, hclean 26 (by simp)]
    · by_cases h84 : k = (84 : Fin 117)
      · subst k
        simp [S₃, S₂, S₁, SR, routeR, movedR, hclean 84 (by simp)]
      · by_cases h85 : k = (85 : Fin 117)
        · subst k
          simp [S₃, S₂, S₁, SR, routeR, movedR, hclean 85 (by simp)]
        · by_cases h89 : k = (89 : Fin 117)
          · subst k
            simp [S₃, S₂, S₁, SR, routeR, movedR, hclean 89 (by simp)]
          · by_cases h26 : k = (26 : Fin 117)
            · subst k
              simp [S₃, S₂, S₁, SR, routeR, movedR, hclean 26 (by simp)]
            · simp [S₃, S₂, S₁, SR, routeR, movedR, h93, h84, h85, h89, h26]

/-- A shared scalar is the singleton-factor specialization of stream cleanup. -/
theorem finish_exec (w : ℕ) (xs ys : List GaussianInt) (a : GaussianInt) (hlen : ys.length = xs.length)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hclean : ∀ k ∈ [(26 : Fin 117), 84, 85, 89], S.R k = []) :
    let SR := { S with R := (Function.update
      (routeR S.R (cstream A w xs) tail (csyms A w a)) 89 (cstream A w ys)) }
    ∃ v', v'.user = v.user ∧
      Exec body finish (mk v SR) (6 * (xs.length * w) + 2 * w + 8)
        (mk v' { S with R := Function.update S.R 93 (cstream A w ys ++ tail) }) := by
  simpa only [cstream_cons, cstream_nil, List.append_nil, List.length_cons,
    List.length_nil, Nat.zero_add, one_mul] using
    finish_stream_exec (body := body) w xs ys [a] hlen v S tail hclean

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
