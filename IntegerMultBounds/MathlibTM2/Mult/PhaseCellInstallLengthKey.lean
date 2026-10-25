module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeUnaryKey

/-! Consume one selected binary key and construct both ordinary row-length
headers required by the raw group solver. All parsing/conversion scratch is
released, and the remaining binary key queue is preserved exactly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def installLengthKey : Pr P 117 Q A U :=
  .seq (takeUnaryKey 115 87 102 0 1 2 3) (ucopy 102 103 4)

theorem installLengthKey_exec (V L : ℕ) (hL : L < 2^V) (suffix : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V)
    (hsrc : S.R 87 = binSyms V L ++ suffix)
    (hfresh : ∀ k ∈ [(0 : Fin 117), 1, 2, 3, 4, 102, 103], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 10*L+19*V+18 ∧
      Exec body installLengthKey (mk v S) n
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R 87 suffix)
          102 (List.replicate L tick)) 103 (List.replicate L tick)) }) := by
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := takeUnaryKey_exec (body := body)
    (width := 115) (src := 87) (dst := 102) (word := 0) (work := 1) (saved := 2) (tmp := 3)
    (by decide) V L hL suffix v S hV hsrc (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update S.R 87 suffix) 102 (List.replicate L tick)) }
  obtain ⟨v₂, hu₂, he₂⟩ := ucopy_exec (body := body) (a := 102) (b := 103) (t := 4)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 4 (by simp))
  have he₂' : Exec body (ucopy 102 103 4) (mk v₁ S₁) (4*L+4)
      (mk v₂ { S₁ with R := Function.update S₁.R 103 (List.replicate L tick) }) := by
    simpa [S₁, hfresh 103 (by simp)] using he₂
  exact ⟨v₂, n₁+(4*L+4), hu₂.trans hu₁, by omega, Exec.seq he₁ he₂'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
