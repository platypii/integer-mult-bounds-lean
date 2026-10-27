module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorNewtonPrelude
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnarySize

/-! Generate the actual logarithmic Newton iteration header and release its complete operand. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryFactorNewtonHeader : Pr P 224 Q A U :=
  .seq boundaryFactorNewtonPrelude (.seq (unarySize 221 191 1 2 3 4 0) (uclear 221))

def boundaryFactorNewtonHeaderCost (p q : ℕ) : ℕ :=
  let n := 256*p*(q+1)
  boundaryFactorNewtonPreludeCost p q+((19*n+8)+(2*n+2))

theorem boundaryFactorNewtonHeader_exec (p q : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hp : (S.R 117).length = 2^15*p) (hq : (S.R 119).length = q)
    (h0 : S.R 0 = []) (h1 : S.R 1 = []) (h2 : S.R 2 = []) (h3 : S.R 3 = []) (h4 : S.R 4 = [])
    (h184 : S.R 184 = []) (h223 : S.R 223 = []) (h221 : S.R 221 = []) (h191 : S.R 191 = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ boundaryFactorNewtonHeaderCost p q ∧
      Exec body boundaryFactorNewtonHeader (mk v S) steps
        (mk v' {S with R := Function.update S.R 191 (List.replicate (factorNewtonSteps p q) tick)}) := by
  let n := 256*p*(q+1)
  let K := factorNewtonSteps p q
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := boundaryFactorNewtonPrelude_exec (body := body) p q v S hp hq h0 h1 h184 h223 h221
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 221 (List.replicate n tick)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := unarySize_exec (body := body)
    (show [(221 : Fin 224),191,1,2,3,4,0].Nodup by decide) n v₁ S₁
    (by simp [S₁]) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · simpa [S₁] using h1
      · simpa [S₁] using h2
      · simpa [S₁] using h3
      · simpa [S₁] using h4
      · simpa [S₁] using h0)
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 191 (List.replicate K tick)}
  have he₂' : Exec body (unarySize 221 191 1 2 3 4 0) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,K,factorNewtonSteps,n,h191] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 221 v₂ S₂
  have hlen : (S₂.R 221).length = n := by simp [S₂,S₁]
  refine ⟨v₃,m₁+(m₂+(2*n+2)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add hm₁ (Nat.add_le_add_right hm₂ _),(Exec.seq he₁ (Exec.seq he₂' he₃)).cast (by rw [hlen]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi221 : i = 221 <;> by_cases hi191 : i = 191 <;> simp [S₂,S₁,K,hi221,hi191,h221]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
