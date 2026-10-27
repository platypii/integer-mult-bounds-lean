module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageComponentTransition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageFinishComponents
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageComponentFrame

/-! Switch and join components in ordinary scratch outside the retained coefficient banks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem placedBoundary_transition {A : ℕ} (S : Stacks 256 A)
    (input parked saved : List (Fin (A+4))) :
    embStk couplingBoundaryReg {S with R := (Function.update (Function.update (Function.update S.R
      110 input) 144 parked) 145 saved)} =
      {embStk couplingBoundaryReg S with R := (Function.update (Function.update (Function.update
        (embStk couplingBoundaryReg S).R 110 input) 144 parked) 145 saved)} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi110 : i = 110
  · subst i; rfl
  by_cases hi144 : i = 144
  · subst i; rfl
  by_cases hi145 : i = 145
  · subst i; rfl
  have h110 : couplingBoundaryReg i ≠ 110 := couplingBoundaryReg_injective.ne hi110
  have h144 : couplingBoundaryReg i ≠ 144 := couplingBoundaryReg_injective.ne hi144
  have h145 : couplingBoundaryReg i ≠ 145 := couplingBoundaryReg_injective.ne hi145
  simp only [embStk,Function.comp_def,Function.update_of_ne hi110,Function.update_of_ne hi144,
    Function.update_of_ne hi145,Function.update_of_ne h110,Function.update_of_ne h144,Function.update_of_ne h145]

theorem placedArithmetic_transition {A : ℕ} (S : Stacks 256 A)
    (input parked saved : List (Fin (A+4))) :
    embStk couplingSourceReg {S with R := (Function.update (Function.update (Function.update S.R
      110 input) 144 parked) 145 saved)} =
      {embStk couplingSourceReg S with R := Function.update (embStk couplingSourceReg S).R 110 input} := by
  change embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg
    (embStk sharedPageRecoveryReg (embStk couplingBoundaryReg {S with R := (Function.update
      (Function.update (Function.update S.R 110 input) 144 parked) 145 saved)}))))) = _
  rw [placedBoundary_transition]
  exact sharedPageArithmetic_transition (embStk couplingBoundaryReg S) input parked saved

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 256 Q A U}

def placedComponentTransition : Pr P 256 Q A U :=
  embProg couplingBoundaryReg Empty.elim (sharedPageComponentTransition (P := Empty))

theorem placedComponentTransition_exec (q s : ℕ) (rhs result next tail outputTail parkedTail : List (Fin (A+4)))
    (hb : rhs.length = s*(2*q+8))
    (hout : result.length = s*(2*q+8)) (hnext : next.length = s*(2*q+8))
    (v : HS 256 Q A U) (S : Stacks 256 A) (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsrc : S.R 110 = rhs++tail) (hresult : S.R 132 = result++outputTail)
    (hparked : S.R 144 = next++parkedTail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (h136 : S.R 136 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cleanComponentTransitionCost q s ∧
      Exec body placedComponentTransition (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          110 (next++tail)) 132 outputTail) 144 parkedTail) 145 (result++S.R 145))}) := by
  let T := embStk couplingBoundaryReg S
  obtain ⟨v₁,n,hu₁,hn,he⟩ := sharedPageComponentTransition_exec (body := fun p : Empty => nomatch p)
    q s rhs result next tail outputTail parkedTail hb hout hnext (embDn couplingBoundaryReg v) T
    hq hs hsrc hresult hparked h94 h131 h134 h135 h136 h147
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingBoundaryReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T₀ : Stacks 240 A := {T with R := Function.update T.R 110 (next++tail)}
  let T₁ : Stacks 240 A := {T₀ with R := Function.update T₀.R 132 outputTail}
  let T₂ : Stacks 240 A := {T₁ with R := Function.update T₁.R 144 parkedTail}
  change embOvr couplingBoundaryReg
    ({T₂ with R := Function.update T₂.R 145 (result++T.R 145)} : Stacks 240 A).get S = _
  rw [embOvr_updR couplingBoundaryReg_injective]
  dsimp only [T₂]
  rw [embOvr_updR couplingBoundaryReg_injective]
  dsimp only [T₁]
  rw [embOvr_updR couplingBoundaryReg_injective]
  dsimp only [T₀]
  rw [embOvr_updR couplingBoundaryReg_injective,embOvr_stk]
  rfl


def placedFinishComponents : Pr P 256 Q A U :=
  embProg couplingBoundaryReg Empty.elim (sharedPageFinishComponents (P := Empty))

theorem placedFinishComponents_exec (hA : 4 ≤ A) (q s : ℕ) (xs ys : List GaussianInt)
    (hxlen : xs.length = s) (hylen : ys.length = s)
    (rhs tail savedTail outputTail original originalTail : List (Fin (A+4)))
    (hrhs : rhs.length = s*(2*q+8)) (horiginal : original.length = s*(2*q+8))
    (v : HS 256 Q A U) (S : Stacks 256 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsource : S.R 110 = rhs++tail) (hx : S.R 145 = cstream A (2*q+8) xs++savedTail)
    (hy : S.R 132 = cstream A (2*q+8) ys++outputTail) (horig : S.R 146 = original++originalTail)
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (h136 : S.R 136 = []) (h140 : S.R 140 = []) (h147 : S.R 147 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cleanFinishComponentsCost q s ∧
      Exec body placedFinishComponents (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          110 (original++tail)) 145 savedTail) 146 originalTail)
          132 (cstream A (2*q+8) (List.zipWith pairComponentWord xs ys)++outputTail))}) := by
  let T := embStk couplingBoundaryReg S
  obtain ⟨v₁,n,hu₁,hn,he⟩ := sharedPageFinishComponents_exec (body := fun p : Empty => nomatch p)
    hA q s xs ys hxlen hylen rhs tail savedTail outputTail original originalTail hrhs horiginal
    (embDn couplingBoundaryReg v) T hq hs hsource hx hy horig h94 h131 h134 h135 h136 h140 h147
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingBoundaryReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T₀ : Stacks 240 A := {T with R := Function.update T.R 110 (original++tail)}
  let T₁ : Stacks 240 A := {T₀ with R := Function.update T₀.R 145 savedTail}
  let T₂ : Stacks 240 A := {T₁ with R := Function.update T₁.R 146 originalTail}
  change embOvr couplingBoundaryReg ({T₂ with R := (Function.update T₂.R 132
    (cstream A (2*q+8) (List.zipWith pairComponentWord xs ys)++outputTail))} : Stacks 240 A).get S = _
  rw [embOvr_updR couplingBoundaryReg_injective]
  dsimp only [T₂]
  rw [embOvr_updR couplingBoundaryReg_injective]
  dsimp only [T₁]
  rw [embOvr_updR couplingBoundaryReg_injective]
  dsimp only [T₀]
  rw [embOvr_updR couplingBoundaryReg_injective,embOvr_stk]
  rfl


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
