module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Host.BinArith

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
  .seq (takePrefix 115 87 0 1 2) (.seq (toUnary 0 102 1 2 3)
    (.seq (ucopy 102 103 4) (uclear 0)))

theorem installLengthKey_exec (V L : ℕ) (hL : L < 2^V) (suffix : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V)
    (hsrc : S.R 87 = binSyms V L ++ suffix)
    (hfresh : ∀ k ∈ [(0 : Fin 117), 1, 2, 3, 4, 102, 103], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 10*L+19*V+18 ∧
      Exec body installLengthKey (mk v S) n
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R 87 suffix)
          102 (List.replicate L tick)) 103 (List.replicate L tick)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := takePrefix_exec (body := body)
    (count := 115) (src := 87) (dst := 0) (buf := 1) (tmp := 2) (by decide)
    v S (binSyms V L) suffix hsrc (by simpa [binSyms] using hV)
    (hfresh 1 (by simp)) (hfresh 2 (by simp))
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update S.R 87 suffix) 0 (binSyms V L)) }
  have he₁' : Exec body (takePrefix 115 87 0 1 2) (mk v S) (6*V+6) (mk v₁ S₁) := by
    simpa [S₁, hfresh 0 (by simp), binSyms] using he₁
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := toUnary_exec_linear body
    (a := 0) (z := 102) (w := 1) (t := 2) (t₂ := 3) (by decide) hL v₁ S₁
    (by simp [S₁]) (by simpa [S₁] using hfresh 1 (by simp))
    (by simpa [S₁] using hfresh 2 (by simp)) (by simpa [S₁] using hfresh 3 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 102 (List.replicate L tick) }
  have he₂' : Exec body (toUnary 0 102 1 2 3) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂, S₁, hfresh 102 (by simp)] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := ucopy_exec (body := body) (a := 102) (b := 103) (t := 4)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂, S₁] using hfresh 4 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 103 (List.replicate L tick) }
  have he₃' : Exec body (ucopy 102 103 4) (mk v₂ S₂) (4*L+4) (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁, hfresh 103 (by simp)] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body 0 v₃ S₃
  have hlen : (S₃.R 0).length = V := by simp [S₃, S₂, S₁, binSyms]
  refine ⟨v₄, (6*V+6)+(n₂+((4*L+4)+(2*V+2))), hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    by omega, (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast (by rw [hlen]) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h0 : k = 0
    · subst k; simp [hfresh 0 (by simp)]
    simp [S₃, S₂, S₁, Function.update_apply, h0]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
