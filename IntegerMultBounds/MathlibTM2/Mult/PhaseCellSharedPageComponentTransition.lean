module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCleanComponentTransition

/-! Park a recovered real component and load the next RHS without releasing the shared boundary page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPageComponentTransition : Pr P 240 Q A U :=
  embProg sharedPageRecoveryReg Empty.elim (cleanComponentTransition (P := Empty))

theorem sharedPageComponentTransition_exec (q s : ℕ) (rhs result next tail outputTail parkedTail : List (Fin (A+4)))
    (hb : rhs.length = s*(2*q+8))
    (hout : result.length = s*(2*q+8)) (hnext : next.length = s*(2*q+8))
    (v : HS 240 Q A U) (S : Stacks 240 A) (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsrc : S.R 110 = rhs++tail) (hresult : S.R 132 = result++outputTail)
    (hparked : S.R 144 = next++parkedTail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (h136 : S.R 136 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cleanComponentTransitionCost q s ∧
      Exec body sharedPageComponentTransition (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          110 (next++tail)) 132 outputTail) 144 parkedTail) 145 (result++S.R 145))}) := by
  let T := embStk sharedPageRecoveryReg S
  obtain ⟨v₁,n,hu₁,hn,he⟩ := cleanComponentTransition_exec (body := fun p : Empty => nomatch p)
    q s rhs result next tail outputTail parkedTail hb hout hnext (embDn sharedPageRecoveryReg v) T
    hq hs hsrc hresult hparked h94 h131 h134 h135 h136 h147
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedPageRecoveryReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T₀ : Stacks 224 A := {T with R := Function.update T.R 110 (next++tail)}
  let T₁ : Stacks 224 A := {T₀ with R := Function.update T₀.R 132 outputTail}
  let T₂ : Stacks 224 A := {T₁ with R := Function.update T₁.R 144 parkedTail}
  change embOvr sharedPageRecoveryReg
    ({T₂ with R := Function.update T₂.R 145 (result++T.R 145)} : Stacks 224 A).get S = _
  rw [embOvr_updR sharedPageRecoveryReg_injective]
  dsimp only [T₂]
  rw [embOvr_updR sharedPageRecoveryReg_injective]
  dsimp only [T₁]
  rw [embOvr_updR sharedPageRecoveryReg_injective]
  dsimp only [T₀]
  rw [embOvr_updR sharedPageRecoveryReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
