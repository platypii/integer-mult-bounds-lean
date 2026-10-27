module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFeedCouplingResult

/-! Feed the computed coupling result to the next solve while preserving both cache keys. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

def placedCouplingResultFeed : Pr P₀ 256 Q A U :=
  embProg couplingSourceReg Empty.elim (feedCouplingResult (P₀ := Empty))

theorem placedCouplingResultFeed_exec (s w : ℕ) (result tail : List (Fin (A+4)))
    (v : HS 256 Q A U) (S : Stacks 256 A)
    (hs : (S.R 97).length = s) (hw : (S.R 94).length = w)
    (hresult : S.R 113 = result++tail) (hlen : result.length = s*w)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 12*s*w+9*s+12 ∧
      Exec body placedCouplingResultFeed (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 113 tail)
          110 (result++S.R 110))}) := by
  let e := couplingSourceReg
  let T := embStk e S
  obtain ⟨vi,m,hu,hm,he⟩ := feedCouplingResult_exec (body := fun p : Empty => nomatch p)
    s w result tail (embDn e v) T hs hw hresult hlen h131 h134 h135
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingSourceReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  let T₁ : Stacks 144 A := {T with R := Function.update T.R 113 tail}
  change embOvr e ({T₁ with R := Function.update T₁.R 110 (result++T.R 110)} : Stacks 144 A).get S = _
  rw [embOvr_updR couplingSourceReg_injective]
  dsimp only [T₁]
  rw [embOvr_updR couplingSourceReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
