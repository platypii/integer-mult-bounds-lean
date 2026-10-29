module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyCountedLine

/-! Reuse the local recovery row count to expose the original RHS and copy it
for coupling. Release the old boundary count, mask and private row count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedRecoveryRhsInput : Pr P 248 Q A U :=
  .seq (retireCountedLine 246 174 110 247 242 243)
    (.seq (copyCountedLine 246 174 110 93 242 243 244) (clearWords [116,167,246]))

def packedRecoveryRhsInputCost (N n w : ℕ) : ℕ :=
  retireCountedLineCost N w+copyCountedLineCost N w+(2*(n+N+N)+7)

theorem packedRecoveryRhsInput_exec (N n w : ℕ)
    (residual rhs tail : List (Fin (A+4))) (hresidual : residual.length = N*w)
    (hrhs : rhs.length = N*w) (v : HS 248 Q A U) (S : Stacks 248 A)
    (hrows : (S.R 246).length = N) (hwidth : (S.R 174).length = w)
    (hcount : (S.R 116).length = n) (hmask : (S.R 167).length = N)
    (hsrc : S.R 110 = residual++(rhs++tail))
    (hclean : ∀ i ∈ ([247,242,243,244] : List (Fin 248)), S.R i = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ packedRecoveryRhsInputCost N n w ∧
      Exec body packedRecoveryRhsInput (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update
          (Function.update (Function.update S.R 110 (rhs++tail)) 93 (rhs++S.R 93))
          116 []) 167 []) 246 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := retireCountedLine_exec (body := body)
    246 174 110 247 242 243 (by decide) N w residual (rhs++tail) hresidual v S hrows hwidth hsrc
    (hclean 247 (by decide)) (hclean 242 (by decide)) (hclean 243 (by decide))
  let S₁ : Stacks 248 A := {S with R := Function.update S.R 110 (rhs++tail)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := copyCountedLine_exec (body := body)
    246 174 110 93 242 243 244 (by decide) N w rhs tail hrhs v₁ S₁
    (by simpa [S₁] using hrows) (by simpa [S₁] using hwidth) (by simp [S₁])
    (by simpa [S₁] using hclean 242 (by decide))
    (by simpa [S₁] using hclean 243 (by decide))
    (by simpa [S₁] using hclean 244 (by decide))
  let S₂ : Stacks 248 A := {S₁ with R := Function.update S₁.R 93 (rhs++S.R 93)}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [(116 : Fin 248),167,246] (by decide) v₂ S₂
  have hsum : ([(116 : Fin 248),167,246].map (fun k => (S₂.R k).length)).sum = n+N+N := by
    simp [S₂,S₁,hcount,hmask,hrows,Nat.add_assoc]
  refine ⟨v₃,m₁+(m₂+(2*(n+N+N)+7)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp only [packedRecoveryRhsInputCost]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h116 : i = 116
    · subst i; simp
    by_cases h167 : i = 167
    · subst i; simp
    by_cases h246 : i = 246
    · subst i; simp
    · simp [S₂,S₁,h116,h167,h246]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
