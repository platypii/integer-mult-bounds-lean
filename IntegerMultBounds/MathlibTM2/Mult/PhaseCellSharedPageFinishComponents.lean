module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCleanFinishComponents

/-! Pair two real outputs and restore the original input while retaining the shared boundary and publication pages. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPageFinishComponents : Pr P 240 Q A U :=
  embProg sharedPageRecoveryReg Empty.elim (cleanFinishComponents (P := Empty))

theorem sharedPageFinishComponents_exec (hA : 4 ≤ A) (q s : ℕ) (xs ys : List GaussianInt)
    (hxlen : xs.length = s) (hylen : ys.length = s)
    (rhs tail savedTail outputTail original originalTail : List (Fin (A+4)))
    (hrhs : rhs.length = s*(2*q+8)) (horiginal : original.length = s*(2*q+8))
    (v : HS 240 Q A U) (S : Stacks 240 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsource : S.R 110 = rhs++tail) (hx : S.R 145 = cstream A (2*q+8) xs++savedTail)
    (hy : S.R 132 = cstream A (2*q+8) ys++outputTail) (horig : S.R 146 = original++originalTail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (h136 : S.R 136 = []) (h140 : S.R 140 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cleanFinishComponentsCost q s ∧
      Exec body sharedPageFinishComponents (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          110 (original++tail)) 145 savedTail) 146 originalTail)
          132 (cstream A (2*q+8) (List.zipWith pairComponentWord xs ys)++outputTail))}) := by
  let T := embStk sharedPageRecoveryReg S
  obtain ⟨v₁,n,hu₁,hn,he⟩ := cleanFinishComponents_exec (body := fun p : Empty => nomatch p)
    hA q s xs ys hxlen hylen rhs tail savedTail outputTail original originalTail hrhs horiginal
    (embDn sharedPageRecoveryReg v) T hq hs hsource hx hy horig h94 h131 h134 h135 h136 h140 h147
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedPageRecoveryReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T₀ : Stacks 224 A := {T with R := Function.update T.R 110 (original++tail)}
  let T₁ : Stacks 224 A := {T₀ with R := Function.update T₀.R 145 savedTail}
  let T₂ : Stacks 224 A := {T₁ with R := Function.update T₁.R 146 originalTail}
  change embOvr sharedPageRecoveryReg ({T₂ with R := (Function.update T₂.R 132
    (cstream A (2*q+8) (List.zipWith pairComponentWord xs ys)++outputTail))} : Stacks 224 A).get S = _
  rw [embOvr_updR sharedPageRecoveryReg_injective]
  dsimp only [T₂]
  rw [embOvr_updR sharedPageRecoveryReg_injective]
  dsimp only [T₁]
  rw [embOvr_updR sharedPageRecoveryReg_injective]
  dsimp only [T₀]
  rw [embOvr_updR sharedPageRecoveryReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
