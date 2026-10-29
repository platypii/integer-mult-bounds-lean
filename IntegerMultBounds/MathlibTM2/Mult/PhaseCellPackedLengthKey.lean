module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeUnaryKey

/-! Consume a generated key once and retain its two required representations. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def packedLengthKey : Pr P 168 Q A U :=
  .seq (uclear 128) (.seq (uclear 157) (takeBinaryUnaryKey 125 126 128 157 134 135 136))

theorem packedLengthKey_exec (V L : ℕ) (hL : L < 2^V) (suffix : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A) (hV : (S.R 125).length = V)
    (hkeys : S.R 126 = binSyms V L++suffix)
    (hfresh : ∀ k ∈ [(134 : Fin 168),135,136], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 2*(S.R 128).length+2*(S.R 157).length+6*L+17*V+16 ∧
      Exec body packedLengthKey (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          126 suffix) 128 (List.replicate L tick)) 157 (binSyms V L))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec body 128 v S
  let S₁ : Stacks 168 A := {S with R := Function.update S.R 128 []}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body 157 v₁ S₁
  let S₂ : Stacks 168 A := {S₁ with R := Function.update S₁.R 157 []}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := takeBinaryUnaryKey_exec (body := body)
    (width := 125) (src := 126) (dst := 128) (word := 157) (work := 134) (saved := 135) (tmp := 136)
    (by decide) V L hL suffix v₂ S₂ (by simpa [S₂,S₁] using hV) (by simpa [S₂,S₁] using hkeys)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · simp [S₂,S₁]
      · simp [S₂]
      · simpa [S₂,S₁] using hfresh 134 (by simp)
      · simpa [S₂,S₁] using hfresh 135 (by simp)
      · simpa [S₂,S₁] using hfresh 136 (by simp))
  refine ⟨v₃,(2*(S.R 128).length+2)+((2*(S.R 157).length+2)+m₃),hu₃.trans (hu₂.trans hu₁),
    by omega,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by simp [S₁]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h128 : k = 128 <;> by_cases h157 : k = 157 <;> by_cases h126 : k = 126 <;>
    simp_all [S₂,S₁,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
