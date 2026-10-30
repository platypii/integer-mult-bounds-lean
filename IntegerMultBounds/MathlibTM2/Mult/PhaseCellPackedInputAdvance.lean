module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Advance past a completed packed input using the retained binary halo length. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedInputAdvance : Pr P 248 Q A U :=
  .seq (toUnary 165 246 0 1 2)
    (.seq (.seq (retireCountedLine 246 174 110 247 242 243)
      (retireCountedLine 246 174 110 247 242 243)) (uclear 246))

def packedInputAdvanceCost (V N w : ℕ) : ℕ :=
  6*N+11*V+6+2*retireCountedLineCost N w+(2*N+2)

theorem packedInputAdvance_exec (V N w : ℕ) (hNV : N < 2^V)
    (residual input tail : List (Fin (A+4)))
    (hresidual : residual.length = N*w) (hinput : input.length = N*w)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hN : S.R 165 = binSyms V N) (hw : (S.R 174).length = w)
    (hsrc : S.R 110 = residual++(input++tail))
    (hclean : ∀ i ∈ ([0,1,2,246,247,242,243] : List (Fin 248)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedInputAdvanceCost V N w ∧
      Exec body packedInputAdvance (mk v S) n
        (mk v' {S with R := Function.update S.R 110 tail}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 246) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v S hN
    (hclean 0 (by decide)) (hclean 1 (by decide)) (hclean 2 (by decide))
  let S₁ : Stacks 248 A := {S with R := Function.update S.R 246 (List.replicate N tick)}
  have he₁' : Exec body (toUnary 165 246 0 1 2) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hclean 246 (by decide),List.append_nil] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := retireCountedLine_pair_exec (body := body)
    246 174 110 247 242 243 (by decide) N w residual input tail hresidual hinput v₁ S₁
    (by simp [S₁]) (by simpa [S₁] using hw) (by simpa [S₁] using hsrc)
    (by simpa [S₁] using hclean 247 (by decide))
    (by simpa [S₁] using hclean 242 (by decide))
    (by simpa [S₁] using hclean 243 (by decide))
  let S₂ : Stacks 248 A := {S₁ with R := Function.update S₁.R 110 tail}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 246 v₂ S₂
  have hcount : (S₂.R 246).length = N := by simp [S₂,S₁]
  refine ⟨v₃,n₁+(n₂+(2*N+2)),hu₃.trans (hu₂.trans hu₁),by
    dsimp only [packedInputAdvanceCost]; omega,?_⟩
  refine (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hcount]) ?_
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = 246 <;> by_cases hj : i = 110 <;> simp [S₂,S₁,hi,hj,hclean 246 (by decide)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
