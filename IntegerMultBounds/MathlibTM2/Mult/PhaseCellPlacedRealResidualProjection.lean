module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedResidualControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealResidualProjection

/-! Execute real projection in ordinary scratch outside both retained cache banks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

def placedRealResidualProjection : Pr P₀ 256 Q A U :=
  embProg couplingSourceReg Empty.elim (realResidualProjection (P₀ := Empty))

theorem placedRealResidualProjection_exec (hA : 4 ≤ A) (q s : ℕ)
    (D R : List GaussianInt) (interiorTail rhsTail : List (Fin (A+4)))
    (hDlen : D.length = s) (hRlen : R.length = s)
    (v : HS 256 Q A U) (S : Stacks 256 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hD : S.R 132 = cstream A (2*q+8) D++interiorTail)
    (hR : S.R 110 = cstream A (2*q+8) R++rhsTail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ realResidualProjectionCost q s ∧
      Exec body placedRealResidualProjection (mk v S) m
        (mk v' {S with R := (Function.update
          (Function.update S.R 132 (cstream A (2*q+8) (D.map realPartWord)++interiorTail))
          110 (cstream A (2*q+8) (R.map realPartWord)++rhsTail))}) := by
  let e := couplingSourceReg
  let T := embStk e S
  obtain ⟨vi,m,hu,hm,he⟩ := realResidualProjection_exec (body := fun p : Empty => nomatch p)
    hA q s D R interiorTail rhsTail hDlen hRlen (embDn e v) T hq hs hD hR h94 h131 h134 h135
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingSourceReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  let T₁ : Stacks 144 A := {T with R := (Function.update T.R 132
    (cstream A (2*q+8) (D.map realPartWord)++interiorTail))}
  change embOvr e ({T₁ with R := (Function.update T₁.R 110
    (cstream A (2*q+8) (R.map realPartWord)++rhsTail))} : Stacks 144 A).get S = _
  rw [embOvr_updR couplingSourceReg_injective]
  dsimp only [T₁]
  rw [embOvr_updR couplingSourceReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
